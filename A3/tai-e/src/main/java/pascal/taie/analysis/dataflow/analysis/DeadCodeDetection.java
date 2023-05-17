/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        int nNodes = cfg.getNumberOfNodes();
        var vis = new ArrayList<Boolean>(nNodes);
        for (int i = 0; i < nNodes; i++) {
            vis.add(false);
        }
        // do BFS
        var q = new LinkedList<Stmt>();
        q.add(cfg.getEntry());
        while (!q.isEmpty()) {
            var fr = q.removeFirst();
            if (fr instanceof If ifStmt) {
                var cond = ConstantPropagation.evaluate((Exp) ifStmt.getCondition(), constants.getInFact(fr));
                if (cond.isUndef()) continue;
                if (cond.isConstant()) {
                    var edges = cfg.getOutEdgesOf(fr);
                    for (var edge : edges) {
                        if (edge.getKind() == Edge.Kind.IF_TRUE && cond.getConstant() == 1) {
                            var nxt = edge.getTarget();
                            if (vis.get(nxt.getIndex())) break;
                            vis.set(nxt.getIndex(), true);
                            q.add(nxt);
                        }
                        if (edge.getKind() == Edge.Kind.IF_FALSE && cond.getConstant() == 0) {
                            var nxt = edge.getTarget();
                            if (vis.get(nxt.getIndex())) break;
                            vis.set(nxt.getIndex(), true);
                            q.add(nxt);
                        }
                    }
                    continue;
                }
                // if it is NAC, fall through and do regular BFS procedural as a normal node
            } else if (fr instanceof SwitchStmt switchStmt) {
                var switchVar = switchStmt.getVar();
                var value = constants.getInFact(fr).get(switchVar);
                if (value.isUndef()) continue;
                if (value.isConstant()) {
                    var intValue = value.getConstant();
                    var case_targets = switchStmt.getCaseTargets();
                    boolean isCaseAllFailed = true;
                    for (var target : case_targets) {
                        if (target.first() == intValue) {
                            isCaseAllFailed = false;
                            var nxt = target.second();
                            if (vis.get(nxt.getIndex())) break;
                            vis.set(nxt.getIndex(), true);
                            q.add(nxt);
                            break;
                        }
                    }
                    if (isCaseAllFailed) {
                        var default_target = switchStmt.getDefaultTarget();
                        var nxt = default_target;
                        if (vis.get(nxt.getIndex())) break;
                        vis.set(nxt.getIndex(), true);
                        q.add(nxt);
                        break;
                    }
                    continue;
                }
                // here is like if
            } else if (fr instanceof AssignStmt<?, ?> assignStmt) {
                var lValue = assignStmt.getLValue();
                if (lValue instanceof Var varr) {
                    var fact = liveVars.getOutFact(fr);
                    if (!fact.contains(varr)) {
                        deadCode.add(fr);
                    }
                }
                // fall through
            }

            for (var nxt : cfg.getSuccsOf(fr)) {
                if (vis.get(nxt.getIndex())) continue;
                vis.set(nxt.getIndex(), true);
                q.add(nxt);
            }
        }
        // merge vis into the last result
        for (var node : cfg) {
            if (!vis.get(node.getIndex()) && node.getLineNumber() > 0) {    // not vis means dead
                deadCode.add(node);
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
