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
		this.turn = 0;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		System.out.println("[" + getMatch().getGame().getName() + " | " + getMatch().getPlayerNamesFromHost() + "] (Turn " + this.turn + ") Score: " + getStateMachine().getGoal(getCurrentState(), getRole()) + " | State: " + getCurrentState());
		this.timeout = timeout - TIMEOUT_BUFFER;
		this.turn++;

		List<Move> actions = getStateMachine().getLegalMoves(getCurrentState(), getRole());
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
			for (int i = 0; i < rootNode.children.length; i++) {
				System.out.print(((i == 0) ? "[" : "") + rootNode.children[i].visits + " (" + actions.get(i) + " : " + (double)rootNode.children[i].utility / rootNode.children[i].visits + ")" + ((i == rootNode.children.length - 1) ? "]\n" : ", "));
			}
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

	class Node {
		Node parent = null;
		MachineState state = null;
		boolean maxnode;

		int visits = 0;
		int utility = 0;
		Node[] children = null;

		public Node(Node parent, MachineState state, boolean maxnode) {
			this.parent = parent; this.state = state; this.maxnode = maxnode;
		}
	}

	private void runMCTS(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
//		System.out.println("Running MCTS");
		Node selectedNode = select(node);
		if (getStateMachine().isTerminal(selectedNode.state)) {
			backpropagate(selectedNode, getStateMachine().findReward(getRole(), selectedNode.state));
			return;
		}
		expand(selectedNode);
		int score = simulate(getRole(), selectedNode, CHARGES_PER_NODE);
		backpropagate(selectedNode, score);
	}

	private Node select(Node node) {
//		System.out.println("In Select");
		if (node.state != null) {
//			System.out.println("- node.state != null");
			if (node.visits == 0) return node;
			if (node.children == null) return node;
			for (Node n : node.children) {
				for (Node nn : n.children) {
					if (nn.visits == 0) return nn;
				}
			}
		}

		double score = 0;
		Node result = node;
		for (Node n : node.children) {
			double newScore = selectfn(n);
			if (newScore > score) {
				score = newScore; result = n;
			}
		}

		return select(result);
	}

	private double selectfn(Node node) {
		return (double)node.utility/node.visits + Math.sqrt(2 * Math.log(node.parent.visits)/node.visits);
	}

	private void expand(Node node) throws MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		List<Move> actions = machine.findLegals(getRole(), node.state);
		node.children = new Node[actions.size()];
		for (int i = 0; i < actions.size(); i++) {
			Node newNode = makeNode(node, null, !node.maxnode);
			node.children[i] = newNode;
			List<List<Move>> jointMoves = machine.getLegalJointMoves(node.state, getRole(), actions.get(i));
			newNode.children = new Node[jointMoves.size()];
			for (int j = 0; j < jointMoves.size(); j++) {
				MachineState s = machine.getNextState(node.state, jointMoves.get(j));
				Node subNewNode = makeNode(newNode, s, !newNode.maxnode);
				newNode.children[j] = subNewNode;
			}
		}
	}

	private int simulate(Role role, Node node, int count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		int total = 0;
		for (int i = 0; i < count; i++) total += depthCharge(role, node.state);
		return total/count;
	}

	private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		while (!machine.isTerminal(state)) {
			state = machine.getNextState(state, machine.getRandomJointMove(state));
		}
		return machine.getGoal(state, role);
	}

	private void backpropagate(Node node, int score) {
		while (true) {
			node.visits++;
			node.utility += score;
			Node parent = node.parent;
			if (parent == null) break;
			if (parent.maxnode) {
				double maxVal = 0.0;
				for (Node child : parent.children) {
					if (child.visits != 0 && (double)child.utility / child.visits > maxVal) maxVal = (double)child.utility / child.visits;
				}
				score = (int)maxVal;
			} else {
				double minVal = Double.POSITIVE_INFINITY;
				for (Node child : parent.children) {
					if (child.visits != 0 && (double)child.utility / child.visits < minVal) minVal = (double)child.utility / child.visits;
				}
				score = (int)minVal;
			}
			node = parent;
		}
	}

	private Node makeNode(Node parent, MachineState state, boolean maxnode) {
		return new Node(parent, state, maxnode);
	}

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
