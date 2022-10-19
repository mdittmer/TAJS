/*
 * Copyright 2021 University of Waterloo
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.tajs;

import ca.uwaterloo.tajs.FlowAnalysisException;
import dk.brics.tajs.analysis.Analysis;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginWithNode;
import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.CatchNode;
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareFunctionNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.DeletePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.EndForInNode;
import dk.brics.tajs.flowgraph.jsnodes.EndLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.EndWithNode;
import dk.brics.tajs.flowgraph.jsnodes.EventDispatcherNode;
import dk.brics.tajs.flowgraph.jsnodes.ExceptionalReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.HasNextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.IfNode;
import dk.brics.tajs.flowgraph.jsnodes.LoadNode;
import dk.brics.tajs.flowgraph.jsnodes.NewObjectNode;
import dk.brics.tajs.flowgraph.jsnodes.NextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.NodeVisitor;
import dk.brics.tajs.flowgraph.jsnodes.NopNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.ThrowNode;
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.WritePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.WriteVariableNode;
import org.apache.log4j.Logger;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.AbstractMap.SimpleEntry;
import java.util.Optional;

import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Controller for flowgraph-based analysis intended for object capability
 * interface definitions.
 */
public class FlowAnalyzer {
  private Analysis analysis;

  /**
   * All variables, organized by function.
   */
  private Map<Function, Set<DeclareVariableNode>> variables;

  /**
   * All 'variable := value' loads, organized by variable.
   */
  private Map<SimpleEntry<Function, DeclareVariableNode>, Set<Integer>> variableValues;

  /**
   * All 'register := value' loads, organized by register ().
   */
  private Map<Integer, Set<LoadNode>> registerValues;

  // TODO: Is this necessary, or can it be rolled into 'registerValues'?
  private Map<Integer, Set<SimpleEntry<Function, DeclareVariableNode>>> registerVariableValues;

  /**
   * A map from base object registers to property writes.
   */
  private Map<Integer, Set<WritePropertyNode>> properties;

  /**
   * A map from call-return-result registers to the associated call nodes.
   */
  private Map<Integer, Set<CallNode>> callReturns;

  private static Logger log = Logger.getLogger(FlowAnalyzer.class);

  public FlowAnalyzer(Analysis analysis) {
    this.analysis = analysis;
    this.variables = newMap();
    this.variableValues = newMap();
    this.registerValues = newMap();
    this.registerVariableValues = newMap();
    this.properties = newMap();
  }

  public void run() {
    log.info("++++++++++++++++  Custom flow analyzer  ++++++++++++++++");
    FlowGraph flowGraph = analysis.getSolver().getFlowGraph();
    for (Function function : flowGraph.getFunctions()) {
      visitFunction(function);
    }
  }

  private void visitFunction(Function function) {
    // TODO: Process function parameters.

    // TODO: Sort topologically as in Function.java's toDot implementation.
    for (BasicBlock basicBlock : function.getBlocks()) {
      visitBasicBlock(basicBlock);
    }
  }

  private void visitBasicBlock(BasicBlock basicBlock) {
    Function function = basicBlock.getFunction();
    for (AbstractNode abstractNode : basicBlock.getNodes()) {
      abstractNode.visitBy((node) -> node.visitBy(new NodeVisitor() {
        @Override
        public void visit(NopNode n) {
        }

        @Override
        public void visit(DeclareVariableNode n) {
          Set<DeclareVariableNode> ownVariables = variables.computeIfAbsent(function, (f) -> newSet());

          String name = n.getVariableName();
          if (ownVariables.stream().anyMatch((ownVariable) -> ownVariable.getVariableName() == name)) {
            throw new FlowAnalysisException("Variable redeclaration");
          }
          ownVariables.add(n);
        }

        @Override
        public void visit(ConstantNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(NewObjectNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(UnaryOperatorNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(BinaryOperatorNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(ReadVariableNode n) {
          // TODO: Shouldn't this just be 'visitLoadNode(n);'?
          int register = n.getResultRegister();
          SimpleEntry<Function, DeclareVariableNode> variable = lookup(function, n.getVariableName());
          Set<SimpleEntry<Function, DeclareVariableNode>> ownRegisterVariableNames = registerVariableValues.computeIfAbsent(register, (r) -> newSet());
          ownRegisterVariableNames.add(variable);
        }

        @Override
        public void visit(WriteVariableNode n) {
          int register = n.getValueRegister();
          SimpleEntry<Function, DeclareVariableNode> variable = lookup(function, n.getVariableName());
          Set<Integer> ownVariableValues = variableValues.computeIfAbsent(variable, (v) -> newSet());
          ownVariableValues.add(register);
        }

        @Override
        public void visit(ReadPropertyNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(WritePropertyNode n) {
          int register = n.getValueRegister();
          Set<WritePropertyNode> ownProperties = properties.computeIfAbsent(register, (r) -> newSet());
          ownProperties.add(n);
        }

        @Override
        public void visit(DeletePropertyNode n) {
        }

        @Override
        public void visit(IfNode n) {
        }

        @Override
        public void visit(DeclareFunctionNode n) {
          visitLoadNode(n);
        }

        @Override
        public void visit(CallNode n) {
          int register = n.getBaseRegister();
          Set<CallNode> ownCallReturns = callReturns.computeIfAbsent(register, (r) -> newSet());
          ownCallReturns.add(n);
        }

        @Override
        public void visit(ReturnNode n) {
        }

        @Override
        public void visit(ExceptionalReturnNode n) {
        }

        @Override
        public void visit(ThrowNode n) {
        }

        @Override
        public void visit(CatchNode n) {
        }

        @Override
        public void visit(BeginWithNode n) {
          // TODO: Does this affect how 'lookup()' should be implemented?
        }

        @Override
        public void visit(EndWithNode n) {
          // TODO: Does this affect how 'lookup()' should be implemented?
        }

        @Override
        public void visit(BeginForInNode n) {
          // TODO: Consider making more precise judgements knowing when nodes may be repeated in a loop.
        }

        @Override
        public void visit(NextPropertyNode n) {
          // TODO: Consider making more precise judgements knowing when nodes may be repeated in a loop.
        }

        @Override
        public void visit(HasNextPropertyNode n) {
        }

        @Override
        public void visit(EventDispatcherNode n) {
          // TODO: Something is needed here if analysis is to follow calls, rather than iterating over all functions.
        }

        @Override
        public void visit(EndForInNode n) {
          // TODO: Consider making more precise judgements knowing when nodes may be repeated in a loop.
        }

        @Override
        public void visit(BeginLoopNode n) {
          // TODO: Consider making more precise judgements knowing when nodes may be repeated in a loop.
        }

        @Override
        public void visit(EndLoopNode n) {
          // TODO: Consider making more precise judgements knowing when nodes may be repeated in a loop.
        }
      }));
    }
  }

  private void visitLoadNode(LoadNode loadNode) {
    int register = loadNode.getResultRegister();
    Set<LoadNode> ownRegisterValues = registerValues.computeIfAbsent(register, (r) -> newSet());
    ownRegisterValues.add(loadNode);
  }

  private SimpleEntry<Function, DeclareVariableNode> lookup(Function function, String name) {
    Set<DeclareVariableNode> ownVariables = variables.get(function);
    Optional<DeclareVariableNode> maybeVariable = ownVariables.stream().filter((v) -> v.getVariableName() == name).findAny();
    if (!maybeVariable.isPresent()) {
      Function outer = function.getOuterFunction();
      if (outer == null) {
        return null;
      } else {
        return lookup(outer, name);
      }
    } else {
      return new SimpleEntry<Function, DeclareVariableNode>(function, maybeVariable.get());
    }
  }
}
