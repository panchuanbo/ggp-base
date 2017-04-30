import java.util.Arrays;
import java.util.List;

import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
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

	private final static int CHARGES_PER_NODE = 500;
	private final static int TIMEOUT_BUFFER = 2500; // 2500ms = 2.5s

	// Stores the timeout (given timeout - buffer)
	long timeout;

	// stores the turn (For debugging)
	int turn = 0;

	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		//which move are we on in the game?
		this.turn = 0;
	}

	//returns the move that our player will make
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		System.out.println("[" + getMatch().getGame().getName() + " | " + getMatch().getPlayerNamesFromHost() + "] (Turn " + this.turn + ") Score: " + getStateMachine().getGoal(getCurrentState(), getRole()) + " | State: " + getCurrentState());

		//the time period we have for deciding move excluding buffer time
		this.timeout = timeout - TIMEOUT_BUFFER;
		this.turn++;

		//what are our player's legal moves?
		List<Move> actions = getStateMachine().getLegalMoves(getCurrentState(), getRole());

		//if only one legal move possible, return immediately
		//NOTE: eventually we should use this time anyway with caching
		if (actions.size() == 1) return actions.get(0);

		Node rootNode = makeNode(null, getCurrentState(), true);
		System.out.println("Got Root Node");

		double bestUtility = 0;
		Move bestAction = actions.get(0);

		int loops_ran = 0;
		while (!reachingTimeout()) {
			loops_ran++;
			// System.out.println("Running MCTS");
			runMCTS(rootNode);
			// System.out.println("Finished Running MCTS");
//			for (int i = 0; i < rootNode.children.length; i++) {
//				System.out.print(((i == 0) ? "[" : "") + rootNode.children[i].visits + " (" + actions.get(i) + " : " + (double)rootNode.children[i].utility / rootNode.children[i].visits + ")" + ((i == rootNode.children.length - 1) ? "]\n" : ", "));
//			}
		}

		for (int i = 0; i < actions.size(); i++) {
			Node n = rootNode.children[i];
			if (n.visits != 0 && (double)n.utility / n.visits > bestUtility) {
				bestUtility = (double)n.utility / n.visits;
				bestAction = actions.get(i);
			}
		}

		System.out.println("(Loops: " + loops_ran + ") Best Action: " + bestAction);

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
		MachineState state = null;
		boolean maxnode; //true if maxnode, false if min-node

		int visits = 0;
		int utility = 0; //sum of the goal values of the terminal states we visit in depth-charges from this node
		Node[] children = null; //all the immediate states following this one

		//constructor
		public Node(Node parent, MachineState state, boolean maxnode) {
			this.parent = parent; this.state = state; this.maxnode = maxnode;
		}
	}

	//Execute the overall MCTS
	//Select node corresponding to current state, expand the tree, do a depth charge, backpropagate
	private void runMCTS(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
//		System.out.println("Running MCTS");

		//Get the node to run depth-charges from
		Node selectedNode = select(node);
		if (getStateMachine().isTerminal(selectedNode.state)) {
			//sketchy - is not sure what to do here
			backpropagate(selectedNode, getStateMachine().findReward(getRole(), selectedNode.state));
			return;
		}

		//expand the tree of selected node - i.e. forming nodes for its children
		expand(selectedNode);

		//do one depth charge from the selected node
		int score = simulateDepthCharge(getRole(), selectedNode, CHARGES_PER_NODE);
		backpropagate(selectedNode, score);
	}

	//choose the node to run depth charges from
	private Node select(Node node) {
		
		//if the given node hasn't been visited, we choose it
		if (node.visits == 0) return node;
		
		//if the node is terminal, we have to choose it
		if (getStateMachine().isTerminal(node.state)) return node;
		
		//go through the immediate next states, and if we haven't visited one, then we choose it
		for (Node n : node.children) {
			if (n.visits == 0) return n;
		}

		//reach this point if we've visited node and all its children at least once
		double bestScore = 0; //the best upper confidence interval for a node
		Node result = node; //node with best score
		
		for (Node n : node.children) {
			double newScore = selectfn(n); //get the score for node n
			if (newScore > score) {
				score = newScore; result = n;
			}
		}

		return select(result); //return node with best score
	}

	//calculate node score, i.e. upper confidence bounds applied to TREES
	//      ^
	//     ^^^
	//		|
	private double selectfn(Node node) {
		return (double)node.utility/node.visits + Math.sqrt(2 * Math.log(node.parent.visits)/node.visits);
	}

	//expand the tree by creating children for the given node
	private void expand(Node node) throws MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		List<Move> actions = machine.findLegals(getRole(), node.state);
		node.children = new Node[actions.size()]; //a list of new nodes
		
		//for each legal move, store the updated state
		for (int i = 0; i < actions.size(); i++) {
			
			//pass in the current state and the move we want to make to update the state
			MachineState nextState = machine.getNextState(node.state, Arrays.asList(actions.get(i))); 
			Node newNode = makeNode(node, nextState, true); //single-player, so we always set maxnode to true
			node.children[i] = newNode; 
		}
	}

	//
	private int simulateDepthCharge(Role role, Node node, int count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		int sumGoalValues = 0; //sums the goal values from all depth charges so far
		for (int i = 0; i < count; i++) sumGoalValues += depthCharge(role, node.state);
		return sumGoalValues/count;
	}

	private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		while (!machine.isTerminal(state)) {
			state = machine.getNextState(state, machine.getRandomJointMove(state));
		}
		return machine.getGoal(state, role);
	}

	private void backpropagate(Node node, int score) {
		while (node != null) {
			node.visits++;
			node.utility += score;
			node = node.parent;
		}
	}

	private Node makeNode(Node parent, MachineState state, boolean maxnode) {
		return new Node(parent, state, maxnode);
	}

	// MARK :- Multiplayer Ignore for now

//	private Node select(Node node) {
////		System.out.println("In Select");
//
//		//state will be null if we have moved but opponent's haven't moved yet
//		//node.state will be null only in multiplayer!
//		if (node.state != null) {
////			System.out.println("- node.state != null");
//
//			//if node hasn't been visited, then we want to select this null
//			if (node.visits == 0) return node;
//
//			//NOTE: this line doesn't make sense - should delete
//			//if (node.children == null) return node;
//
//			//node.children is our legal immediate moves
//			for (Node n : node.children) {
//
//				//n.children is the
//				for (Node nn : n.children) {
//					if (nn.visits == 0) return nn;
//				}
//			}
//		}
//
//		double score = 0;
//		Node result = node;
//		for (Node n : node.children) {
//			double newScore = selectfn(n);
//			if (newScore > score) {
//				score = newScore; result = n;
//			}
//		}
//
//		return select(result);
//	}

//	private void expand(Node node) throws MoveDefinitionException, TransitionDefinitionException {
//		StateMachine machine = getStateMachine();
//		List<Move> actions = machine.findLegals(getRole(), node.state);
//		node.children = new Node[actions.size()];
//		for (int i = 0; i < actions.size(); i++) {
//			Node newNode = makeNode(node, null, !node.maxnode);
//			node.children[i] = newNode;
//			List<List<Move>> jointMoves = machine.getLegalJointMoves(node.state, getRole(), actions.get(i));
//			newNode.children = new Node[jointMoves.size()];
//			for (int j = 0; j < jointMoves.size(); j++) {
//				MachineState s = machine.getNextState(node.state, jointMoves.get(j));
//				Node subNewNode = makeNode(newNode, s, !newNode.maxnode);
//				newNode.children[j] = subNewNode;
//			}
//		}
//	}
//
//	private int simulateDepthCharge(Role role, Node node, int count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		int total = 0;
//		for (int i = 0; i < count; i++) total += depthCharge(role, node.state);
//		return total/count;
//	}
//
//	private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
//		StateMachine machine = getStateMachine();
//		while (!machine.isTerminal(state)) {
//			state = machine.getNextState(state, machine.getRandomJointMove(state));
//		}
//		return machine.getGoal(state, role);
//	}
//
//	private void backpropagate(Node node, int score) {
//		while (true) {
//			node.visits++;
//			node.utility += score;
//			Node parent = node.parent;
//			if (parent == null) break;
//			if (parent.maxnode) {
//				double maxVal = 0.0;
//				for (Node child : parent.children) {
//					if (child.visits != 0 && (double)child.utility / child.visits > maxVal) maxVal = (double)child.utility / child.visits;
//				}
//				score = (int)maxVal;
//			} else {
//				double minVal = Double.POSITIVE_INFINITY;
//				for (Node child : parent.children) {
//					if (child.visits != 0 && (double)child.utility / child.visits < minVal) minVal = (double)child.utility / child.visits;
//				}
//				score = (int)minVal;
//			}
//			node = parent;
//		}
//	}
//
//	private Node makeNode(Node parent, MachineState state, boolean maxnode) {
//		return new Node(parent, state, maxnode);
//	}

	// END MCTS IMPLEMENTATION
	// ----------------------------------------------------------------------------------------------------------------

	// ----------------------------------------------------------------------------------------------------------------
	// BEGIN UTILITY/HELPER METHODS

	private boolean reachingTimeout() {
		return System.currentTimeMillis() > this.timeout;
	}

	// END UTILITY/HELPER METHODS
	// ----------------------------------------------------------------------------------------------------------------
}
