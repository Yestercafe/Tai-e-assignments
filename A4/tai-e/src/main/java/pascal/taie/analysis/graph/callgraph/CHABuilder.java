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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeSpecial;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        var q = new LinkedList<JMethod>();
        q.add(entry);
        // do memorized BFS
        while (!q.isEmpty()) {
            var fr = q.removeFirst();
            if (!callGraph.contains(fr)) {
                callGraph.addReachableMethod(fr);
                for (var ir : fr.getIR()) {
                    if (ir instanceof Invoke cs) {
                        var t = resolve(cs);
                        for (var targetMethod : t) {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs.getRValue()), cs, targetMethod));
                            q.add(targetMethod);
                        }
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> t = new HashSet<>();
        var invokeExp = callSite.getRValue();
        var m = callSite.getMethodRef().getSubsignature();
        switch (CallGraphs.getCallKind(invokeExp)) {
            case STATIC -> t.add(invokeExp.getMethodRef().getDeclaringClass().getDeclaredMethod(m));
            case SPECIAL -> t.add(dispatch(callSite.getMethodRef().getDeclaringClass(), m));
            case VIRTUAL, INTERFACE -> {
                var c = callSite.getMethodRef().getDeclaringClass();
                var q = new LinkedList<JClass>();
                q.add(c);
                while (!q.isEmpty()) {   // access all direct and indirect subclasses ans subinterfaces
                    var fr = q.removeFirst();
                    t.add(dispatch(fr, m));
                    if (fr.isInterface()) {
                        q.addAll(hierarchy.getDirectSubinterfacesOf(fr));
                        q.addAll(hierarchy.getDirectImplementorsOf(fr));
                    } else {
                        q.addAll(hierarchy.getDirectSubclassesOf(fr));
                    }
                }
            }
        }
        t.remove(null);
        return t;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        var realMethod = jclass.getDeclaredMethod(subsignature);
        if (realMethod != null && !realMethod.isAbstract()) {
            return realMethod;
        }
        if (jclass.getSuperClass() == null) {
            return null;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
