import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class MCTSTeapotPlayer extends StateMachineGamer {

	Player p;

	private final static int CHARGES_PER_NODE = 5;
	private final static int TIMEOUT_BUFFER = 2500; // 2500ms = 2.5s
	private final static int BRIAN_C_FACTOR = 50; // tl;dr 2 != 100 (find paper to read)
	private final static int NUMBER_OF_MAX_THREADS = 3;
	private final static boolean MULTITHREADING_ENABLED = false;
	private final static double NANOSECOND_IN_SECOND = 1000000000.0;
	private final static boolean TESTING_SOMETHING = false;

	// Stores the timeout (given timeout - buffer)
	long timeout;

	// stores the turn (For debugging)
	int turn = 0;
	int level = 0;

	// c-value decay
	double[] decayValues;

	// stores time spent in each step of MCTS (debugging)
	long selectTime = 0, expandTime = 0, depthChargeTime = 0, backpropTime = 0;

	// stores the current game thread [not in use]
	Thread gameSearcherThread;

	// debugging
	StateMachine backupStateMachine;

	Node root_node;

	int depthCharges = 0;

	@Override
	public StateMachine getInitialStateMachine() {
//		return new CachedStateMachine(new ProverStateMachine());
//		return new CachedStateMachine(new BabyPropnetStateMachine());
		return new CachedStateMachine(new FirstStepsPropnetStateMachine());
//		return new CachedStateMachine(new HopefullyBetterPropnetStateMachineQuestionMark());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// setup multithreading machines
		List<Gdl> rules = getMatch().getGame().getRules();
		this.backupStateMachine = new ProverStateMachine();
		this.backupStateMachine.initialize(rules);
		for (int i = 0; i < NUMBER_OF_MAX_THREADS; i++) {
			this.machines[i] = new FirstStepsPropnetStateMachine();
			this.machines[i].initialize(rules);
		}

		this.decayValues = new double[100];
		for (int i = 1; i <= this.decayValues.length; i++) {
			this.decayValues[i-1] = 1/(Math.pow(i, 0.25));
			System.out.print("" + this.decayValues[i-1] + ", ");
		}

//		this.root_node = makeNode(null, getCurrentState(), true, null);
//		while (System.currentTimeMillis() < timeout - TIMEOUT_BUFFER) {
//			try {
//				runMCTS(this.root_node);
//			} catch (InterruptedException | ExecutionException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//		}

		this.turn = 0;
	}

	//returns the move that our player will make
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		System.out.println("Begin Select Move");
		System.out.println("[" + getMatch().getGame().getName() + " | " + getMatch().getPlayerNamesFromHost() + "] (Turn " + this.turn + ") Score: " + getStateMachine().getGoal(getCurrentState(), getRole()) + " | State: " + getCurrentState());

		//the time period we have for deciding move excluding buffer time
		this.timeout = timeout - TIMEOUT_BUFFER;
		this.turn++;
		this.depthCharges = 0;
		selectTime = expandTime = depthChargeTime = backpropTime = 0;

		//what are our player's legal moves?
		List<Move> actions = getStateMachine().getLegalMoves(getCurrentState(), getRole());

		//if only one legal move possible, return immediately
		if (actions.size() == 1) return actions.get(0);

		Node rootNode = makeNode(null, getCurrentState(), true, null);
		System.out.println("Got Root Node with State: " + getCurrentState());

		double bestUtility = 0;
		Move bestAction = actions.get(0);

		int loops_ran = 0;
		while (!reachingTimeout()) {
			loops_ran++;
			try {
				runMCTS(rootNode);
			} catch (InterruptedException | ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			if (rootNode.finishedComputing) break;
		}

		System.out.println("Done running MCTS: (Depth Charges: " + this.depthCharges + ") (MCTS Loops: " + loops_ran + ")");

		for (int i = 0; i < actions.size(); i++) {
			Node n = rootNode.children[i];
			if (n != null) {
				if (n.finishedComputing && n.actual_utility == 100) return n.action;
				if (n.finishedComputing) {
					bestUtility = n.actual_utility;
					bestAction = actions.get(i);
					System.out.println("Finished computing the subtree...");
				} else {
					if (n.visits != 0 && n.utility / n.visits > bestUtility) {
						bestUtility = n.utility / n.visits;
						bestAction = actions.get(i);
					}
				}
			} else {
				System.out.println("WE ARE NOT EXPANDING CORRECTLY");
			}
		}

		System.out.println("(Depth Charges: " + this.depthCharges + ") (MCTS Loops: " + loops_ran + ")" + "Best Action: " + bestAction + " Score: " + bestUtility);
		System.out.println("Select Time: " + this.selectTime/NANOSECOND_IN_SECOND + " | Expand Time: " + this.expandTime/NANOSECOND_IN_SECOND + " | DC Time: " + this.depthChargeTime/NANOSECOND_IN_SECOND + " | Backprop Time: " + this.backpropTime/NANOSECOND_IN_SECOND);

		return bestAction;
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "418 I'm The Next Teapot";
	}

	// ----------------------------------------------------------------------------------------------------------------
	// BEGIN MCTS IMPLEMENTATION

	//A node is essentially a state of the game, also tracks other info
	class Node {
		Node parent = null;
		Move action = null;
		MachineState state = null;
		int indexInParent = 0;

		boolean maxnode; //true if maxnode, false if min-node
		boolean finishedComputing = false;

		int visits = 0;
		double utility = 0; //sum of the goal values of the terminal states we visit in depth-charges from this node
		double actual_utility = 0;

		int expandedUpTo = 0; // node we've expanded up too
		BitSet finishedChildren;
		Node[] children = null; //all the immediate states following this one

		// debug data
		int level = 0;

//		ArrayList<Double> scores = new ArrayList<Double>();
		//constructor
		public Node(Node parent, MachineState state, boolean maxnode, Move action) {
			this.parent = parent; this.state = state; this.maxnode = maxnode; this.action = action;
		}
	}

	//Execute the overall MCTS
	//Select node corresponding to current state, expand the tree, do a depth charge, backpropagate
	private void runMCTS(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException, InterruptedException, ExecutionException {
		// System.out.println("Running MCTS");
		//Get the node to run depth-charges from
		long start = 0;

		start = System.nanoTime();
		Node selectedNode = select(node);
		if (getStateMachine().isTerminal(selectedNode.state)) {
//			System.out.println("Found Terminal: " + selectedNode.state);
			selectedNode.finishedComputing = true;
			//sketchy - is not sure what to do here --> well, jeffrey says it's okay;
			if (reachingTimeout()) return;
			if (selectedNode.visits == 0) {
				backpropagate(selectedNode, getStateMachine().findReward(getRole(), selectedNode.state));
			} else {
				backpropagate(selectedNode, selectedNode.utility/selectedNode.visits);
			}
			this.selectTime += (System.nanoTime() - start);
			return;
		}
		this.selectTime += (System.nanoTime() - start);

		//expand the tree of selected node - i.e. forming nodes for its children
		start = System.nanoTime();
		Node result = expand(selectedNode);
		this.expandTime += (System.nanoTime() - start);

		if (!TESTING_SOMETHING) {
			//do one depth charge from the selected node
			if (MULTITHREADING_ENABLED) {
				start = System.nanoTime();
				List<Future<Double>> results = executor.invokeAll(Arrays.asList(
						new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[0])
						, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[1])
						//, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[2])
				));
				for (Future<Double> f : results) {
					this.depthCharges += CHARGES_PER_NODE;
					backpropagate(result, f.get());
				}
				this.backpropTime += (System.nanoTime() - start);
			} else {
				start = System.nanoTime();
				double score = simulateDepthCharge(getRole(), result, CHARGES_PER_NODE);
				this.depthChargeTime += (System.nanoTime() - start);

				start = System.nanoTime();
				backpropagate(result, score);
				this.backpropTime += (System.nanoTime() - start);
			}
		} else { // TESTING SOMETHIGN HAHAHAHAHHAHAHAHAH
			if (!result.finishedComputing) {
				if (MULTITHREADING_ENABLED) {
					start = System.nanoTime();
					List<Future<Double>> results = executor.invokeAll(Arrays.asList(
							new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[0])
							, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[1])
							//, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[2])
					));
					for (Future<Double> f : results) {
						this.depthCharges += CHARGES_PER_NODE;
						backpropagate(result, f.get());
					}
					this.backpropTime += (System.nanoTime() - start);
				} else {
					start = System.nanoTime();
					double score = simulateDepthCharge(getRole(), result, CHARGES_PER_NODE);
					this.depthChargeTime += (System.nanoTime() - start);

					start = System.nanoTime();
					backpropagate(result, score);
					this.backpropTime += (System.nanoTime() - start);
				}
			} else {
				start = System.nanoTime();
				backpropagate(result, result.actual_utility);
				this.backpropTime += (System.nanoTime() - start);
			}
		}
	}

	private Node select(Node node) {
		if (getStateMachine().isTerminal(node.state) || node.finishedComputing) return node;
		if (node.visits == 0) return node;
		if (node.children == null || node.expandedUpTo != node.children.length) return node;

		double score = Double.NEGATIVE_INFINITY;
		Node result = node;
		for (Node n : node.children) {
			double newScore = (!n.finishedComputing) ? selectfn(n) : n.actual_utility;
			if (newScore >= score) {
				score = newScore; result = n;
			}
		}

		return select(result);
		/*
		if (node.expandedUpTo != node.children.length) return node;
		if (node.visits == 0) return node;
		if (getStateMachine().isTerminal(node.state)) return node;

		//node.children is our legal immediate moves
		for (Node n : node.children) if (n.visits == 0) return n;

		double score = 0;
		Node result = node;
		for (Node n : node.children) {
			double newScore = selectfn(n);
			// System.out.println("New Score: " + newScore + " | Old Score: " + score);
			if (newScore >= score) {
				score = newScore; result = n;
			}
		}

		return select(result);
		*/
	}

	private Node expand(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
		int expandedUpTo = node.expandedUpTo;
		StateMachine machine = getStateMachine();
		if (node.children == null) {
			List<Move> actions = machine.getLegalMoves(node.state, getRole());
			node.children = new Node[actions.size()];
			node.finishedChildren = new BitSet(actions.size());
		}
		if (node.children.length <= expandedUpTo) return node;
		if (node.children[expandedUpTo] == null) {
			List<Move> actions = machine.getLegalMoves(node.state, getRole());
			node.children[expandedUpTo] = makeNode(node, node.state, !node.maxnode, actions.get(expandedUpTo));
			node.children[expandedUpTo].indexInParent = expandedUpTo;
		}
		int childExpandedUpTo = node.children[expandedUpTo].expandedUpTo;
		List<Move> jointMove = null;
		if (node.children[expandedUpTo].children == null) {
			List<List<Move>> jointMoves = machine.getLegalJointMoves(node.children[expandedUpTo].state, getRole(), node.children[expandedUpTo].action);
			node.children[expandedUpTo].children = new Node[jointMoves.size()];
			node.children[expandedUpTo].finishedChildren = new BitSet(jointMoves.size());
			jointMove = jointMoves.get(childExpandedUpTo);
		} else {
			jointMove = machine.getLegalJointMoves(node.children[expandedUpTo].state, getRole(), node.children[expandedUpTo].action).get(childExpandedUpTo);
		}
		MachineState nextState = machine.getNextState(node.children[expandedUpTo].state, jointMove);
		node.children[expandedUpTo].children[childExpandedUpTo] = makeNode(node.children[expandedUpTo], nextState, node.maxnode, null);
		node.children[expandedUpTo].children[childExpandedUpTo].indexInParent = childExpandedUpTo;
		node.children[expandedUpTo].expandedUpTo++;
		if (node.children[expandedUpTo].expandedUpTo == node.children[expandedUpTo].children.length) node.expandedUpTo++;
		if (machine.isTerminal(nextState)) {
			node.children[expandedUpTo].children[childExpandedUpTo].finishedComputing = true;
			node.children[expandedUpTo].children[childExpandedUpTo].actual_utility = machine.getGoal(nextState, getRole());
		}

		return node.children[expandedUpTo].children[childExpandedUpTo];
		/*
		StateMachine machine = getStateMachine();
		List<Move> actions = machine.findLegals(getRole(), node.state);
		if (node.children == null) node.children = new Node[actions.size()];
		if (node.action == null) {
			for (int i = 0; i < actions.size(); i++) {
				Node newNode = makeNode(node, node.state, !node.maxnode, actions.get(i));
				node.children[i] = newNode;
			}
		} else {
			List<List<Move>> jointMoves = machine.getLegalJointMoves(node.state, getRole(), node.action);
			node.children = new Node[jointMoves.size()];
			for (int i = 0; i < jointMoves.size(); i++) {
				MachineState nextState = machine.getNextState(node.state, jointMoves.get(i));
				Node newNode = makeNode(node, nextState, !node.maxnode, null);
				node.children[i] = newNode;
			}
		}
		*/
	}

	private double simulateDepthCharge(Role role, Node node, double count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		double total = 0, i = 0;
		for (; i < count; i++) {
			if (reachingTimeout() && i != 0) break;
			total += depthCharge(role, node.state);
		}
		return (i == 0) ? 0 : total/i;
	}

	private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		this.depthCharges++;
		StateMachine machine = getStateMachine();
		while (!machine.isTerminal(state)) state = machine.getNextState(state, machine.getRandomJointMove(state));
//		System.out.println("depth charge done: " + this.depthCharges);
		return machine.getGoal(state, role);
	}


	private void backpropagate(Node node, double score) {
		while (true) {
			node.visits++;
			node.utility += score;
			Node parent = node.parent;
			if (parent == null) break;
			parent.finishedChildren.set(node.indexInParent, node.finishedComputing);
			if (parent.finishedChildren.cardinality() == parent.children.length) {
				parent.finishedComputing = true;
				if (parent.maxnode) {
					double maxval = 0;
					for (Node n : parent.children) {
						if (n.actual_utility > maxval) maxval = n.actual_utility;
					}
//					System.out.println("maxval: " + maxval);
					parent.actual_utility = maxval;
				} else {
					double minval = 100;
					for (Node n : parent.children) {
						if (n.actual_utility < minval) minval = n.actual_utility;
					}
//					System.out.println("minval: " + minval + " | num childs: " + parent.children.length + " | level: " + parent.level + " | pos: " + parent.indexInParent);
					parent.actual_utility = minval;
				}
				score = parent.actual_utility;
			}
			node = parent;

		}
//		while (node != null) {
//			node.visits++;
//			node.utility += score;
//			// node.scores.add(score);
//			node = node.parent;
//		}
	}

	private double selectfn(Node node) {
		double decay = 1;
		if (this.turn >= this.decayValues.length) decay = this.decayValues[99];
		else decay = this.decayValues[this.turn];

		if (node.maxnode) return node.utility/node.visits + decay * BRIAN_C_FACTOR * Math.sqrt(Math.log(node.parent.visits)/node.visits);
		else {
			double val = -node.utility/node.visits + decay * BRIAN_C_FACTOR * Math.sqrt(Math.log(node.parent.visits)/node.visits);
			return val;
			//return (val < 0) ? 0 : val;
		}
	}

	private Node makeNode(Node parent, MachineState state, boolean maxnode, Move action) {
		Node newNode = new Node(parent, state, maxnode, action);
		if (parent != null) newNode.level = parent.level + 1;
		else newNode.level = 0;
		return newNode;
	}

	// END MCTS IMPLEMENTATION
	// ----------------------------------------------------------------------------------------------------------------

	// BEGIN MULTITHREADING
	// ----------------------------------------------------------------------------------------------------------------

	ExecutorService executor = Executors.newFixedThreadPool(NUMBER_OF_MAX_THREADS);
	StateMachine machines[] = new StateMachine[NUMBER_OF_MAX_THREADS];

	class DepthCharger implements Callable<Double> {

		private Role role;
		private Node node;
		private double count;
		private StateMachine machine;

		private double simulateDepthCharge(Role role, Node node, double count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
			double total = 0, i = 0;
			for (; i < count; i++) {
				if (reachingTimeout() && i != 0) break;
				total += depthCharge(role, node.state);
			}
			return (i == 0) ? 0 : total/i;
		}

		private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
			while (!machine.isTerminal(state)) {
				state = machine.getNextState(state, machine.getRandomJointMove(state));
			}
			return machine.getGoal(state, role);
		}

		public DepthCharger(Role role, Node node, double count, StateMachine machine) {
			this.role = role;
			this.node = node;
			this.count = count;
			this.machine = machine;
//			System.out.println(role + " " + count + " " + machine);
		}

	    @Override
	    public Double call() throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
	        return simulateDepthCharge(this.role, this.node, this.count);
	    }
	}


	// ----------------------------------------------------------------------------------------------------------------
	// END MULTITHREADING

	// ----------------------------------------------------------------------------------------------------------------
	// BEGIN UTILITY/HELPER METHODS
	private static double variance(ArrayList<Double> list) {
		if (list.size() < 5) return 15;
		double sumDiffsSquared = 0.0;
		double avg = 0.0;
		for (Double d : list) avg += d;
		avg /= list.size();
		for (double value : list) {
			double diff = value - avg;
		    diff *= diff;
		    sumDiffsSquared += diff;
		}
		return sumDiffsSquared  / list.size();
	}

	private boolean reachingTimeout() {
		return System.currentTimeMillis() > this.timeout;
	}

	// END UTILITY/HELPER METHODS
	// ----------------------------------------------------------------------------------------------------------------
}
