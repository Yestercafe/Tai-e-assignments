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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var ret = new CPFact();
        for (var param : cfg.getIR().getParams()) {
            ret.update(param, Value.getNAC());
        }
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((k, v) -> {
            target.update(k, meetValue(target.get(k), v));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.getConstant() == v2.getConstant()) {  // v1 and v2 must be constants here
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    /**
     * F: OUT[s] = gen | (IN[s] - {(x, _})
     *
     * @param stmt
     * @param in
     * @param out
     * @return
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var oldOut = out.copy();
        meetInto(in, out);

        if (stmt instanceof DefinitionStmt definitionStmt) {
            var lValue_ = definitionStmt.getLValue();
            if (lValue_ instanceof Var lValue) {
                var rValue= definitionStmt.getRValue();
                out.update(lValue, evaluate(rValue, in));
            }
        }

        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral intLiteral) {   // never reach?
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof BinaryExp binaryExp) {
            var op1_ = binaryExp.getOperand1();
            var op2_ = binaryExp.getOperand2();

            if (!canHoldInt(op1_) || !canHoldInt(op2_)) {
                return Value.getUndef();
            }
            var op1 = in.get(op1_);
            var op2 = in.get(op2_);
            if (op1.isNAC() || op2.isNAC()) {
                if (op2.isConstant() && op2.getConstant() == 0) {   // op1 is NAC
                    if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                        switch (arithmeticExp.getOperator()) {
                            case DIV, REM -> {
                                return Value.getUndef();
                            }
                        }
                    }
                }
                return Value.getNAC();
            } else if (op1.isConstant() && op2.isConstant()) {
                int ans = 0;
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> ans = op1.getConstant() + op2.getConstant();
                        case SUB -> ans = op1.getConstant() - op2.getConstant();
                        case MUL -> ans = op1.getConstant() * op2.getConstant();
                        case DIV -> {
                            if (op2.getConstant() == 0) return Value.getUndef();
                            ans = op1.getConstant() / op2.getConstant();
                        }
                        case REM -> {
                            if (op2.getConstant() == 0) return Value.getUndef();
                            ans = op1.getConstant() % op2.getConstant();
                        }
                    }
                } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case AND -> ans = op1.getConstant() & op2.getConstant();
                        case OR -> ans = op1.getConstant() | op2.getConstant();
                        case XOR -> ans = op1.getConstant() ^ op2.getConstant();
                    }
                } else if (binaryExp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> ans = op1.getConstant() == op2.getConstant() ? 1 : 0;
                        case NE -> ans = op1.getConstant() != op2.getConstant() ? 1 : 0;
                        case LT -> ans = op1.getConstant() < op2.getConstant() ? 1 : 0;
                        case LE -> ans = op1.getConstant() <= op2.getConstant() ? 1 : 0;
                        case GT -> ans = op1.getConstant() > op2.getConstant() ? 1 : 0;
                        case GE -> ans = op1.getConstant() >= op2.getConstant() ? 1 : 0;
                    }
                } else if (binaryExp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> ans = op1.getConstant() << op2.getConstant();
                        case SHR -> ans = op1.getConstant() >> op2.getConstant();
                        case USHR -> ans = op1.getConstant() >>> op2.getConstant();
                    }
                } else {
                    return Value.getNAC();
                }
                return Value.makeConstant(ans);
            } else {
                return Value.getUndef();
            }
        }
        // maybe function invocation, such as `invokevirtual`, return an undecidable value
        return Value.getNAC();
    }
}
