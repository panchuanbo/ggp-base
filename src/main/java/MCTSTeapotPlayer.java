import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.apache.commons.math3.stat.correlation.PearsonsCorrelation;
import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class MCTSTeapotPlayer extends StateMachineGamer {
	Player p;

	private final static int CHARGES_PER_NODE = 5;
	private final static int TIMEOUT_BUFFER = 2500; // 2500ms = 2.5s
	private final static double BRIAN_C_FACTOR = 12.5; // tl;dr 2 != 100 (find paper to read)
	private final static int NUMBER_OF_MAX_THREADS = 2;
	private final static boolean MULTITHREADING_ENABLED = false;
	private final static double NANOSECOND_IN_SECOND = 1000000000.0;
	private final static boolean TESTING_SOMETHING = false;
	private final static boolean KEEP_TREE = true;
	private final static int NEUTRAL_NODE = 0;
	private final static int LOSS_NODE = -1;
	private final static int WIN_NODE = 1;
	private final static int TERMINAL_NODE = 2;
	private final static int HUMAN_TIMEOUT_BUFFER = 45000;
	private final static boolean HUMAN_PLAYER = true;

	private HopefullyBetterPropnetStateMachineQuestionMark PROPNET_STATEMACHINE = null;

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

	// keep track of the root node
	Node rootNode;

	boolean enableGoalHeuristic = false;
	double goalRSquared = 0.0;

	int depthCharges = 0;
	int[] depthChargesMultithreading = new int[NUMBER_OF_MAX_THREADS];

	int numberOfRoles = 0;

	// C-VALUE
	ArrayList<Double> allScores;
	double standardDev = 1.0;
	private double extraCFactor = 1.0;

	Proposition initProposition = null;
	ArrayList<Move> solverMoves;
	boolean solved = false;

	private boolean isZeroSum = false;

	@Override
	public StateMachine getInitialStateMachine() {
//		return new CachedStateMachine(new ProverStateMachine());
//		return new CachedStateMachine(new BabyPropnetStateMachine());
//		return new CachedStateMachine(new FirstStepsPropnetStateMachine());
//		return new FirstStepsPropnetStateMachine();
		this.PROPNET_STATEMACHINE = new HopefullyBetterPropnetStateMachineQuestionMark();
		return this.PROPNET_STATEMACHINE;
	}

	public static double[] convertDoubles(List<Double> doubles) {
	    double[] ret = new double[doubles.size()];
	    Iterator<Double> iterator = doubles.iterator();
	    for (int i = 0; i < ret.length; i++)
	    {
	        ret[i] = iterator.next().doubleValue();
	    }
	    return ret;
	}

	public void runDFSCompileComp(List<Set<Component>> sepGamesComps, Component childOfTermInput, int gameNum) {
		if (childOfTermInput == null || sepGamesComps.get(gameNum).contains(childOfTermInput)) {
			return;
		} else if (childOfTermInput.isBase() || childOfTermInput.isInput()) {
			//childOfTermInput.visited = true;
			sepGamesComps.get(gameNum).add(childOfTermInput);
			for (Component output: childOfTermInput.getOutputs()) {
				if (!(sepGamesComps.get(gameNum).contains(output))) {
					runDFSCompileComp(sepGamesComps, output, gameNum);
				}
			}
			return;
		} else {
			//childOfTermInput.visited = true;
			sepGamesComps.get(gameNum).add(childOfTermInput);
			for (Component output: childOfTermInput.getOutputs()) {
				if (!(sepGamesComps.get(gameNum).contains(output))) {
					runDFSCompileComp(sepGamesComps, output, gameNum);
				}
			}
			for (Component input: childOfTermInput.getInputs()) {
				if (!(sepGamesComps.get(gameNum).contains(input))) {
					runDFSCompileComp(sepGamesComps, input, gameNum);
				}
			}
			return;
		}
	}

	private void forwardprop(Component c, boolean start) {
		if (c == null) return;
		if (c.connectedToTerminal) return;
		c.connectedToTerminal = true;
		if (c.isBase() && !start) return;
		for (Component cc : c.getOutputs()) forwardprop(cc, false);
	}

	private boolean checkCounter(Component c) {
//		if (!((c instanceof Transition) || c.isBase())) return false;
		if (c.numberOfInputs() == 0) {
			if (c.isBase()) return true;
			if (this.initProposition != null && c.equals(this.initProposition)) return true;
		}
		else if (c.numberOfInputs() == 1) return checkCounter(c.fasterGetSingleInput());
		else if (c.numberOfInputs() != 1) return false;
		return false;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		System.out.println("Entered Metagame");
		System.out.println("GAME: " + this.getMatch().toString());
		this.turn = 0;
		// At this point the propnet has been built with the metagame

		// setup multithreading machines
		List<Gdl> rules = getMatch().getGame().getRules();
		this.backupStateMachine = new ProverStateMachine();
		this.backupStateMachine.initialize(rules);

//		/* Beginning of the factoring for MCTS */
//		PropNet p = PROPNET_STATEMACHINE.propnet;
//		// Collection of pointers to all components in the propnet
//		Set<Component> components = p.getComponents();
//		Proposition terminalProp = p.getTerminalProposition();
//		Set<Component> inputsToTerm = terminalProp.getInputs();
//		if (terminalProp.getInputs().size() != 1) {
//			System.out.println("stateMachineMetaGame: There is not exactly 1 input to the terminal prop");
//		}
//		terminalProp.removeAllInputs();
//		List<Set<Component>> sepGamesComps = null;
//		for(Component input : inputsToTerm) {
//			if (!(input instanceof Or)) {
//				sepGamesComps = new ArrayList<Set<Component>>(1);
//				sepGamesComps.add(components);
//			} else {
//				// set parent to be a terminal node and then DFS through and copy into a new state machine to pass to runMCTS
//				sepGamesComps = new ArrayList<Set<Component>>(input.getInputs().size());
//				int gameNum = 0;
//				for (Component childOfTermInput: input.getInputs()) {
//					// Mark each childOfTermInput as a terminal node
//					if (!(childOfTermInput instanceof Proposition)) {
//						System.out.println("childOfTermInput is not a Proposition");
//					}
//					Proposition chilPropOfTermInput = (Proposition) childOfTermInput;
//					for (Component compOfSepGame: childOfTermInput.getInputs()) {
//						compOfSepGame.addOutput(terminalProp);
//						terminalProp.addInput(compOfSepGame);
//						runDFSCompileComp(sepGamesComps, childOfTermInput, gameNum);
//						compOfSepGame.removeOutput(childOfTermInput);
//					}
//					sepGamesComps.get(gameNum).add((Component) terminalProp);
//
//
//
//
//
//					gameNum++;
//				}
//			}
//		}
//
//		List<Set<Component>> uniqueSubPropnetsSetComps = null;
//		for (Set<Component> gameSetComps: sepGamesComps) {
//			if (!(uniqueSubPropnetsSetComps.contains(gameSetComps))) {
//				uniqueSubPropnetsSetComps.add(gameSetComps);
//			}
//		}
//
//		for (Set<Component> gameSetComps: uniqueSubPropnetsSetComps) {
//			// Make a new subpropnet using roles and getSetComps
//			PropNet subGameP = new PropNet(p.getRoles(), gameSetComps);
//			// Make a new thread
//			Thread thread = new Thread() {
//				@Override
//				public void run() {
////					runMCTS(......);
//				}
//			};
//			thread.start();
//			// This will return as soon as thread starts and will not wait until the run method is done
//		}

		// Initialization of debug variables
		this.numberOfRoles = getStateMachine().getRoles().size();
		this.rootNode = null;
		this.level = 0;
		this.allScores = new ArrayList<>();
		this.standardDev = 1.0;
		this.solverMoves = new ArrayList();
		this.solved = false;
		this.extraCFactor = 5000;
		this.isZeroSum = false;

		if ((getStateMachine() instanceof HopefullyBetterPropnetStateMachineQuestionMark)) {
			System.out.println("[Metagame] Propnet StateMachine Exists!");
			// FACTOR OUT THE STEP COUNTER (If it exists that is...)
			int numberOfSteps = 0;
			HopefullyBetterPropnetStateMachineQuestionMark m = (HopefullyBetterPropnetStateMachineQuestionMark)getStateMachine();
			PropNet propnet = m.propnet;
			this.isZeroSum = m.zeroSum;
			try {
				this.initProposition = propnet.getInitProposition();
				Proposition terminalProp = propnet.getTerminalProposition();
				if ((terminalProp.fasterGetSingleInput() instanceof Or)) {
					Component or = terminalProp.fasterGetSingleInput();
					for (Component c : or.fasterGetInputs()) {
						if (checkCounter(c)) {
							int ctr = 0;
							Component cc = c;
							while (cc.numberOfInputs() != 0) {
								if (cc.isBase()) ctr++;
								cc = cc.fasterGetSingleInput();
							}
							System.out.println("[Metagame] Found Step Counter: " + ctr);
							numberOfSteps = ctr;
							break;
						}
					}
				}
			} catch (Exception e) {
			}

			System.out.println("[Metagame] Can't Find Step Counter");
			if (numberOfSteps == 0) numberOfSteps = 100;

			// check if I can factor...
			int uselessRoles = 0;
			if (propnet.getRoles().size() > 1) {
				Map<Role, Set<Proposition>> rolePropMap = new HashMap<>();
				for (Role r : propnet.getRoles()) {
					Set<Proposition> sp = new HashSet<>();
					for (Proposition p : propnet.getLegalPropositions().get(r)) {
						Proposition does = propnet.getLegalInputMap().get(p);
						forwardprop(does, false);
					}
					for (Proposition p : propnet.getBasePropositions().values()) {
						if (p.connectedToTerminal) sp.add(p);
					}
					for (Component c : propnet.getComponents()) c.connectedToTerminal = false;
					for (Proposition p : sp) {
						forwardprop(p, true);
					}
					for (Proposition p : propnet.getBasePropositions().values()) {
						if (p.connectedToTerminal) sp.add(p);
					}
					for (Component c : propnet.getComponents()) c.connectedToTerminal = false;
					rolePropMap.put(r, sp);
				}

				Set<Proposition> mySet = rolePropMap.get(getRole());
				for (Role r : propnet.getRoles()) {
					if (r.equals(getRole())) continue;
					Set<Proposition> mine = new HashSet<>(mySet);
					Set<Proposition> theirs = rolePropMap.get(r);
					mine.retainAll(theirs);
					if (mine.size() == 0) uselessRoles++;
				}

				System.out.println("[Metagame] Useless roles: " + uselessRoles);
			}

			// EVERYTHING HERE IS SINGLE PLAYER SOLVER
			try{
				if (this.numberOfRoles - uselessRoles == 1) {
				    PrintWriter writer = new PrintWriter("input.txt", "UTF-8");
					System.out.println("[Metagame] Found Single Player Game!");
					System.out.println("[Metagame] SOLVER ON");
					System.out.println("[Metagame] Begin Conversion of GDL from Prefix --> Answer Set Programming");
					for (Gdl g : m.propnet.processedGameDescription) {
						String s = g.toASPString();
						s = s.replaceAll("[?]", "Var");
						if (s.contains(",T)")) {
							if (s.contains(":-")) s += ", time(T)";
							else s += " :- time(T)";
						} else if (s.contains("(T)")) {
							if (s.contains(":-")) s += ", time(T)";
							else s += " :- time(T)";
						}
						s += ".";
						writer.println(s);
					}
					writer.println("1 { does(R,M,T) : input(R,M) } 1 :- role(R), not terminated(T), time(T).");
					writer.println("terminated(T) :- terminal(T), time(T).");
					writer.println("terminated(T+1) :- terminated(T), time(T).");
					writer.println(":- does(R,M,T), not legal(R,M,T).");
					writer.println(":- 0 { terminated(T) : time(T) } 0.");
					writer.println(":- terminated(T), not terminated(T-1), role(R), not goal(R,100,T).");
					writer.println("time(1.." + numberOfSteps + ").");
				    writer.close();
				    System.out.println("[Metagame] Finished conversion");

				    Role r = getRole();
				    Set<Proposition> legalProps = propnet.getLegalPropositions().get(r);
				    Map<String, Move> tempMap = new HashMap<>();
				    for (Proposition pp : legalProps) {
				    	Proposition does = propnet.getLegalInputMap().get(pp);
				    	String doesString = does.getName().infixString();
				    	doesString = doesString.replaceAll("\\s+","");

				    	tempMap.put(doesString, m.getMoveFromProposition(pp));
				    }
				    // System.out.println("[Metagame] Solver Map " + tempMap);

				    System.out.println("[Metagame] Running solver");
				    Process p = Runtime.getRuntime().exec(new String[]{"C:\\clingo-5.2.0-win64\\clingo.exe","input.txt"});
				    BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));

				    String line = "";
		        	ArrayList<String> temp = new ArrayList<String>();
		        	while (true) {
				    	if (timeout - TIMEOUT_BUFFER - 1500 < System.currentTimeMillis()) {
				    		p.destroy();
				    		break;
				    	}
		        		if (reader.ready()) {
					    	if (reader.read() == -1) break;
		        			line = reader.readLine();
				        	String[] tokens = line.split(" ");
				        	for (String s : tokens) {
				        		if (s.contains("does")) {
				        			System.out.println("[" + getRole().toString() + "]");
				        			if (this.numberOfRoles != 1) {
				        				if (s.contains(getRole().toString())) {
						        			System.out.println("[Metagame] Found " + s);
						        			temp.add(s);
				        				}
				        			} else {
					        			System.out.println("[Metagame] Found " + s);
					        			temp.add(s);
				        			}
				        		}
				        	}
		        		}
		        	}
//				    while ((line = reader.readLine())!= null) {
//				    	if (timeout - TIMEOUT_BUFFER - 1000 < System.currentTimeMillis()) {
//				    		p.destroy();
//				    		break;
//				    	}
//			        	String[] tokens = line.split(" ");
//			        	for (String s : tokens) {
//			        		if (s.contains("does")) {
//			        			System.out.println("[" + getRole().toString() + "]");
//			        			if (this.numberOfRoles != 1) {
//			        				if (s.contains(getRole().toString())) {
//					        			System.out.println("[Metagame] Found " + s);
//					        			temp.add(s);
//			        				}
//			        			} else {
//				        			System.out.println("[Metagame] Found " + s);
//				        			temp.add(s);
//			        			}
//			        		}
//			        	}
//				    }
				    p.waitFor(timeout - System.currentTimeMillis() - TIMEOUT_BUFFER - 1500, TimeUnit.MILLISECONDS);
				    System.out.println("[Metagame] Solver complete!");

				    solverMoves = new ArrayList<>();
				    for (int i = 0; i < temp.size(); i++) solverMoves.add(null);
				    for (String s : temp) {
	        			String[] parts = s.split(",");
	        			String lastPart = parts[parts.length - 1];
	        			lastPart = lastPart.replaceAll("[^0-9]", "");
	        			int index = Integer.parseInt(lastPart);
	        			s += ";";
	        			String sol = s.replaceAll(",[0-9]+?[)];", ")");
	        			solverMoves.set(index-1, tempMap.get(sol));
				    }
				    System.out.println("[Metagame] Potentially solved with moves " + solverMoves);
				    if (solverMoves.size() > 0) {
				    	this.solved = true;
				    	for (int i = 0; i < solverMoves.size(); i++) {
				    		if (solverMoves.get(i) == null) {
				    			this.solved = false;
				    			break;
				    		}
				    	}
				    }
				}
			} catch (Exception e) {
				System.out.println("error: " + e);
			}

			if (this.solved) {
				System.out.println("[Metagame] Processing complete! Game solved :)");
				return;
			} else {
				System.out.println("[Metagame] Nevermind... Not solved :(");
			}
		}

		this.decayValues = new double[100];
		for (int i = 1; i <= this.decayValues.length; i++) {
			this.decayValues[i-1] = 1/(Math.pow(i, 0.25));
		}

		long timeLeft = timeout - System.currentTimeMillis() - TIMEOUT_BUFFER;

		// HEURISTICS

		StateMachine machine = getStateMachine();
		Role role = getRole();
		MachineState state = getCurrentState();
		int gamesSimulated = 0;
		ArrayList<Double> terminalScores = new ArrayList<Double>(Arrays.asList(0.));
		ArrayList<Double> ourGoalValues = new ArrayList<Double>(Arrays.asList(0.));
		while (System.currentTimeMillis() + timeLeft/2 < timeout - TIMEOUT_BUFFER) {
			if (machine.isTerminal(state)) { // done
				int goal = machine.getGoal(state, role);
				terminalScores.set(gamesSimulated, (double)goal); terminalScores.add(0.);
				ourGoalValues.add(0.);
				// oppMobilityValues.add(0.); oppFocusValues.add(0.);

				gamesSimulated++;
				machine = getStateMachine();
				role = getRole();
				state = getCurrentState();
			}

			List<Move> actions = machine.getLegalMoves(state, role);
			Move randomMove = actions.get((new Random()).nextInt(actions.size()));

			if (actions.size() != 1) { // if there is only one possible move, don't let that effect the overall outcome
				ourGoalValues.set(gamesSimulated, ourGoalValues.get(gamesSimulated) + machine.getGoal(state, role));
			}

			List<Move> randomJointMove = machine.getRandomJointMove(state, role, randomMove);
			state = machine.getNextState(state, randomJointMove);
		}
		double[] ts = convertDoubles(terminalScores);
		double[] ourGV = convertDoubles(ourGoalValues);

		// CALCULATE HEURISTICS

		try {
			PearsonsCorrelation pc = new PearsonsCorrelation();
			goalRSquared = pc.correlation(ourGV, ts);
			System.out.println("[Metagame] GOAL R^2: " + goalRSquared);
			if (goalRSquared > 0.25) this.enableGoalHeuristic = true;
			System.out.println("[Metagame] Games Simulated: " + gamesSimulated);

			this.timeout = timeout - TIMEOUT_BUFFER;
			rootNode = makeNode(null, getCurrentState(), true, null);
			System.out.println("\n[Metagame] Initial State: " + getCurrentState());
			while (!reachingTimeout()) {
				try {
					runMCTS(rootNode);
				} catch (InterruptedException | ExecutionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		} catch (Exception e) {

		}
	}

	//returns the move that our player will make
	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		System.out.println("Begin Select Move");
		System.out.println("[ SELECT MOVE | " + this.getName() + "] (Turn " + this.turn + ") Score: " + getStateMachine().getGoal(getCurrentState(), getRole()) + " | State: " + getCurrentState());

		//the time period we have for deciding move excluding buffer time
		this.timeout = timeout - ((HUMAN_PLAYER) ? HUMAN_TIMEOUT_BUFFER : TIMEOUT_BUFFER);
		this.turn++;
		this.depthCharges = 0;
		selectTime = expandTime = depthChargeTime = backpropTime = 0;
		this.allScores.clear();
		for (int i = 0; i < NUMBER_OF_MAX_THREADS; i++) depthChargesMultithreading[i] = 0;

		if (this.solved) {
			Move s = this.solverMoves.get(0);
			this.solverMoves.remove(0);
			return s;
		}

		//what are our player's legal moves?
		List<Move> actions = getStateMachine().getLegalMoves(getCurrentState(), getRole());

		if (KEEP_TREE) {
			if (!rootNode.state.equals(getCurrentState())) {
				boolean found = false;
				for (Node n : rootNode.children) {
					if (n != null) {
						for (Node nn : n.children) {
							if (nn != null) {
//								System.out.println("__STATE: " + nn.state);
								if (nn.state.equals(getCurrentState())) {
									found = true;
									rootNode = nn;
									rootNode.parent = null;
									break;
								}
							}
						}
					}
					if (found) break;
				}
				if (!found) {
					System.out.println("NOT FOUND: REGENERATING");
					rootNode = makeNode(null, getCurrentState(), true, null);
				} else {
//					System.out.println("FOUND, RESETTING ROOT NODE (" + rootNode.visits + ", " + rootNode.utility/rootNode.visits + ")");
				}
			}

			//if only one legal move possible, return immediately
			if (actions.size() == 1) {
				while (!reachingTimeout()) {
					this.extraCFactor = 5000;
					try {
						runMCTS(rootNode);
					} catch (InterruptedException | ExecutionException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
				return actions.get(0);
			}
		} else {
			rootNode = makeNode(null, getCurrentState(), true, null);
			if (actions.size() == 1) return actions.get(0);
		}

//		Node rootNode = makeNode(null, getCurrentState(), true, null);
//		System.out.println("Got Root Node with State: " + getCurrentState());
//		System.out.println("Legal Moves: " + actions);

		if (getStateMachine().isTerminal(getCurrentState())) {
			System.out.println("[Select Move] ERROR: WE ARE ON A TERMINAL STATE");
		}

		double bestUtility = 0;
		Move bestAction = actions.get(0);

		// check to see if we've already solved this game:
		if (rootNode.children != null) {
			for (Node n : rootNode.children) {
				if (n != null && n.status == WIN_NODE) {
					System.out.println("[Select Move] Solver: " + n.action);
					return n.action;
				}
			}
		}

		int loops_ran = 0;
		while (!reachingTimeout()) {
			this.extraCFactor = 1;
			loops_ran++;
			try {
				runMCTS(rootNode);
			} catch (InterruptedException | ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			if (rootNode.children != null) {
				for (Node n : rootNode.children) {
					if (n != null && n.status == WIN_NODE) {
						System.out.println("[SOLVER] " + n.action);
						return n.action;
					}
				}
			}
//			if (rootNode.children != null) {
//				for (Node n : rootNode.children) {
//					if (n != null && n.finishedComputing && n.actual_utility == 100) return n.action;
//				}
//			}
//			if (rootNode.finishedComputing) break;
		}

		Move bestLossAction = null;
		double bestLossScore = Double.NEGATIVE_INFINITY;
		int numberLost = 0;
		System.out.println("Move Results: ");
		for (int i = 0; i < actions.size(); i++) {
			Node n = rootNode.children[i];
			if (n != null) {
				if (n.status == LOSS_NODE) {
					System.out.println("\t" + n.action + ": LOSS");
					numberLost++;
					if (n.visits != 0 && n.utility / n.visits > bestLossScore) {
						bestLossScore = n.utility / n.visits;
						bestLossAction = actions.get(i);
					}
					continue;
				} else if (n.status == WIN_NODE) {
					System.out.println("\t" + n.action + ": WIN");
				}
				if (n.finishedComputing && n.actual_utility == 100) {
					System.out.println("Solved: " + actions.get(i));
					return n.action;
				}
				if (n.finishedComputing) {
					System.out.println("\t" + n.action + " (actual): " + n.actual_utility);
					if (n.actual_utility > bestUtility) {
						bestUtility = n.actual_utility;
						bestAction = actions.get(i);
						System.out.println("Finished computing the subtree...");
					}
				} else {
					System.out.println("\t" + n.action + ": " + n.utility / ((n.visits == 0) ? 1 : n.visits));
					if (n.visits != 0 && n.utility / n.visits > bestUtility) {
						bestUtility = n.utility / n.visits;
						bestAction = actions.get(i);
					}
				}
			} else {
				System.out.println("[Select Move] WE ARE NOT EXPANDING CORRECTLY");
			}
		}

		if (MULTITHREADING_ENABLED) this.depthCharges = 0;
		for (int i = 0; i < NUMBER_OF_MAX_THREADS; i++) this.depthCharges += this.depthChargesMultithreading[i];

		System.out.println("[Select Move] (Depth Charges: " + this.depthCharges + ") (MCTS Loops: " + loops_ran + ")" + "Best Action: " + bestAction + " Score: " + bestUtility + " Depth: " + (this.level - this.rootNode.level));
		System.out.println("[Select Move] Select Time: " + this.selectTime/NANOSECOND_IN_SECOND + " | Expand Time: " + this.expandTime/NANOSECOND_IN_SECOND + " | DC Time: " + this.depthChargeTime/NANOSECOND_IN_SECOND + " | Backprop Time: " + this.backpropTime/NANOSECOND_IN_SECOND);

		if (numberLost == actions.size()) {
			System.out.println("[Select Move] We lost... Selecting best move...");
			return bestLossAction;
		}
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
		double mean = 0;
		double variance = 0;

		// SOLVER
		int status = NEUTRAL_NODE;
		BitSet finishedChildren;

		// HEURISTICS
		double heuristic = 0.0;
		double heuristicCtr = 0.0;

		int expandedUpTo = 0; // node we've expanded up too
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
		if (selectedNode.finishedComputing || getStateMachine().isTerminal(selectedNode.state)) {
//			System.out.println("Backprop Finished Node");
			if (reachingTimeout()) return;
			this.backpropagate(selectedNode, selectedNode.actual_utility);
			this.selectTime += (System.nanoTime() - start);
			return;
		}
		if (selectedNode.status == WIN_NODE || selectedNode.status == LOSS_NODE) {
			if (reachingTimeout()) return;
			this.backpropagate(selectedNode, (selectedNode.status == WIN_NODE) ? 100 : 0);
			this.selectTime += (System.nanoTime() - start);
			return;
		}
		this.selectTime += (System.nanoTime() - start);

		//expand the tree of selected node - i.e. forming nodes for its children
		start = System.nanoTime();
		Node result = expand(selectedNode);
		this.expandTime += (System.nanoTime() - start);

		//do one depth charge from the selected node
		if (MULTITHREADING_ENABLED) {
			start = System.nanoTime();
			List<Future<Double>> results = executor.invokeAll(Arrays.asList(
					new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[0], 0)
					, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[1], 1)
					//, new DepthCharger(getRole(), result, CHARGES_PER_NODE, machines[2])
			));
			for (Future<Double> f : results) {
				backpropagate(result, f.get());
			}
			this.backpropTime += (System.nanoTime() - start);
		} else {
			start = System.nanoTime();
			double score = simulateDepthCharge(getRole(), result, CHARGES_PER_NODE);
			this.depthChargeTime += (System.nanoTime() - start);
			this.allScores.add(score);
			if (this.allScores.size() >= 50 && this.allScores.size() <= 1000 && this.allScores.size() % 50 == 0) computeStdDev();
			start = System.nanoTime();
			backpropagate(result, score);
			this.backpropTime += (System.nanoTime() - start);
		}
	}

	private Node select(Node node) throws GoalDefinitionException {
		if (getStateMachine().isTerminal(node.state) || node.finishedComputing) return node;
		if (node.status != NEUTRAL_NODE) return node;
//		if (getStateMachine().isTerminal(node.state)) return node;
		if (node.visits == 0) return node;
		if (node.children == null || node.expandedUpTo != node.children.length) return node;

		double score = Double.NEGATIVE_INFINITY, score_solved = Double.NEGATIVE_INFINITY;
		Node result = null, result_solved = null;
		for (Node n : node.children) {
			// attempt #2
			if (this.isZeroSum || this.numberOfRoles == 1) {
				if (n.status != NEUTRAL_NODE) {
					double newScore = selectfn(n, node.variance);
					if (newScore >= score_solved) {
						score_solved = newScore; result_solved = n;
					}
				} else {
					double newScore = selectfn(n, node.variance);
					if (newScore >= score) {
						score = newScore; result = n;
					}
				}
			} else {
				// attempt #1
				if (n.finishedComputing) {
					double newScore = n.actual_utility;
					if (newScore >= score_solved) {
						score_solved = newScore; result_solved = n;
					}
				} else {
					double newScore = selectfn(n, node.variance);
					if (newScore >= score) {
						score = newScore; result = n;
					}
				}
			}
		}

		if (result == null) {
//			System.out.println("GOT SOLVED BRANCH");
			return select(result_solved);
		}
		return select(result);
	}

	private Node expand(Node node) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
		int expandedUpTo = node.expandedUpTo;
		StateMachine machine = getStateMachine();
		if (node.children == null) {
			List<Move> actions = machine.getLegalMoves(node.state, getRole());
			node.children = new Node[actions.size()];
			for (int i = 0; i < actions.size(); i++) {
				node.children[i] = this.makeNode(node, node.state, !node.maxnode, actions.get(i));
				node.children[i].indexInParent = i;
			}
			node.finishedChildren = new BitSet(actions.size());
		}
		if (node.children.length <= expandedUpTo) {
			System.out.println("This is not supposed to be called...");
			return node;
		}
		int childExpandedUpTo = node.children[expandedUpTo].expandedUpTo;
		if (node.children[expandedUpTo].children == null) {
			List<List<Move>> jointMoves = machine.getLegalJointMoves(node.children[expandedUpTo].state, getRole(), node.children[expandedUpTo].action);
			node.children[expandedUpTo].children = new Node[jointMoves.size()];
			for (int i = 0; i < jointMoves.size(); i++) {
				MachineState nextState = machine.getNextState(node.children[expandedUpTo].state, jointMoves.get(i));
				node.children[expandedUpTo].children[i] = this.makeNode(node.children[expandedUpTo], nextState, node.maxnode, null);
				node.children[expandedUpTo].children[i].indexInParent = i;
			}
			node.children[expandedUpTo].finishedChildren = new BitSet(jointMoves.size());
		}
		node.children[expandedUpTo].expandedUpTo++;
		if (node.children[expandedUpTo].expandedUpTo == node.children[expandedUpTo].children.length) node.expandedUpTo++;
		MachineState stateInQuestion = node.children[expandedUpTo].children[childExpandedUpTo].state;
		if (machine.isTerminal(stateInQuestion)) {
			int score = machine.getGoal(stateInQuestion, getRole());
//			System.out.println("Terminal State with Score: " + score);
//			node.children[expandedUpTo].children[childExpandedUpTo].finishedComputing = true;
			node.children[expandedUpTo].children[childExpandedUpTo].actual_utility = score;
			if (this.numberOfRoles == 1) {
				if (score == 100) {
					System.out.println("[SOLVER] Found Win!");
					node.children[expandedUpTo].children[childExpandedUpTo].status = WIN_NODE;
				}
			} else {
				if (this.isZeroSum) {
					if (score == 100) {
						node.children[expandedUpTo].children[childExpandedUpTo].status = LOSS_NODE;
					} else if (score == 0) {
						node.children[expandedUpTo].children[childExpandedUpTo].status = WIN_NODE;
					} else { // lol
						node.children[expandedUpTo].children[childExpandedUpTo].status = TERMINAL_NODE;
					}
				} else {
					node.children[expandedUpTo].children[childExpandedUpTo].finishedComputing = true;
					node.children[expandedUpTo].children[childExpandedUpTo].actual_utility = score;
				}
			}
		}

		return node.children[expandedUpTo].children[childExpandedUpTo];
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
		int increment = 1;
		while (true) {
			if (node.finishedComputing) score = node.actual_utility;
			node.visits += increment;
			node.utility += score;
			Node parent = node.parent;
			if (node.visits > 1) {
				if (node.variance == -1) node.variance = 1;
				double nextVariance = (node.visits - 2)/(double)(node.visits - 1) * node.variance + 1.0/node.visits * Math.pow(score - node.mean, 2);
				node.variance = nextVariance;
			} else {
				node.variance = -1;
			}
			if (node.visits >= 1) {
				double nextMean = (score + (node.visits - 1)*node.mean)/node.visits;
				node.mean = nextMean;
			}
			if (parent == null) break;
//			if (parent.visits == 0 && node.visits == 2 && !node.finishedComputing) { // didn't prop heuristics
//				 increment += 1;
//				 score = node.utility;
//			}
			if (this.numberOfRoles == 1) {
				if (node.status == WIN_NODE) parent.status = WIN_NODE;
			} else {
				if (this.isZeroSum) {
					if (node.status == WIN_NODE) {
						parent.status = LOSS_NODE;
					} else if (node.status == LOSS_NODE) {
						int num_loss = 0;
						int num_loss_tie = 0;
						for (Node cc : parent.children) {
							if (cc.status == LOSS_NODE) num_loss++;
							if (cc.status == LOSS_NODE || cc.status == TERMINAL_NODE) num_loss_tie++;
						}
						if (num_loss == parent.children.length) parent.status = WIN_NODE;
						else if (num_loss_tie == parent.children.length) parent.status = TERMINAL_NODE;
//						parent.finishedChildren.set(node.indexInParent, true);
//						if (parent.finishedChildren.cardinality() == parent.children.length) {
//							parent.status = WIN_NODE;
//						}
					}
				} else {
					parent.finishedChildren.set(node.indexInParent, node.finishedComputing);
					if (parent.finishedChildren.cardinality() == parent.children.length) {
						parent.finishedComputing = true;
//						System.out.println("Solved a subtree...");
						if (parent.maxnode) {
							double maxval = 0;
							for (Node n : parent.children) {
								if (n.actual_utility > maxval) maxval = n.actual_utility;
							}
//							System.out.println("maxval: " + maxval + " | num childs: " + parent.children.length + " | level: " + parent.level + " | pos: " + parent.indexInParent);
							parent.actual_utility = maxval;
						} else {
							double minval = 100;
							for (Node n : parent.children) {
								if (n.actual_utility < minval) minval = n.actual_utility;
							}
//							System.out.println("minval: " + minval + " | num childs: " + parent.children.length + " | level: " + parent.level + " | pos: " + parent.indexInParent);
							parent.actual_utility = minval;
						}
//						System.out.println("Now Gonna Prop This: " + parent.actual_utility + " instead of " + score);
						score = parent.actual_utility;
					}
				}
			}
			node = parent;

		}
	}

	private double selectfn(Node node, double variance) throws GoalDefinitionException {
		double decay = 1;
		if (this.turn >= this.decayValues.length) decay = this.decayValues[99];
		else decay = this.decayValues[this.turn];

		double avgUtility = (node.finishedComputing) ? node.actual_utility : node.utility/node.visits;
		double heuristic = 0;

		double stdDev = this.standardDev;
		if (variance > 0) {
			stdDev = Math.sqrt(variance);
		}

		double c_value = BRIAN_C_FACTOR * stdDev;
//		if (this.extraCFactor == 1) c_value = BRIAN_C_FACTOR * stdDev;
//		else if (node.maxnode) c_value = BRIAN_C_FACTOR * stdDev;
//		else c_value = this.extraCFactor;

//		double heuristic = (node.heuristicCtr == 0) ? 0 : node.heuristic/node.heuristicCtr;
//		if (node.finishedComputing) return (node.maxnode) ? avgUtility : -avgUtility;
		if (node.finishedComputing && node.actual_utility == 0) return Double.NEGATIVE_INFINITY;

		if (node.maxnode) return -(avgUtility + heuristic) + c_value * Math.sqrt(Math.log(node.parent.visits)/node.visits);
		else {
			return (avgUtility + heuristic) + c_value * Math.sqrt(Math.log(node.parent.visits)/node.visits);
		}
	}

	private Node makeNode(Node parent, MachineState state, boolean maxnode, Move action) throws GoalDefinitionException {
		Node newNode = new Node(parent, state, maxnode, action);
		if (state != null) {
			double goal = 0.0;
			if (this.enableGoalHeuristic) {
				goal = getStateMachine().getGoal(state, getRole());
				newNode.heuristic = goal;
				newNode.heuristicCtr = 1.0;
				Node p = newNode.parent;
				if (p != null) {
					p.heuristic += goal;
					p.heuristicCtr++;
				}
			}
		}
		if (parent != null) newNode.level = parent.level + 1;
		if (newNode.level > this.level) this.level = newNode.level;
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
		private int index = 0;

		private double simulateDepthCharge(Role role, Node node, double count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
			double total = 0, i = 0;
			for (; i < count; i++) {
				if (reachingTimeout() && i != 0) break;
				total += depthCharge(role, node.state);
			}
			return (i == 0) ? 0 : total/i;
		}

		private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
			depthChargesMultithreading[this.index]++;
			while (!machine.isTerminal(state)) {
				state = machine.getNextState(state, machine.getRandomJointMove(state));
			}
			return machine.getGoal(state, role);
		}

		public DepthCharger(Role role, Node node, double count, StateMachine machine, int index) {
			this.role = role;
			this.node = node;
			this.count = count;
			this.machine = machine;
			this.index = index;
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
	private void computeStdDev() {
		if (this.allScores.size() % 50 == 0) {
			double sumDiffsSquared = 0.0;
			double avg = 0.0;
			for (Double d : this.allScores) avg += d;
			avg /= this.allScores.size();
			for (double value : this.allScores) {
				double diff = Math.pow(value - avg, 2);
			    sumDiffsSquared += diff;
			}
			this.standardDev = Math.sqrt(sumDiffsSquared  / this.allScores.size());
			if (this.allScores.size() == 1000) System.out.println("" + this.allScores.size() + " Items with StdDev: " + this.standardDev);
		}
	}

	private boolean reachingTimeout() {
		return System.currentTimeMillis() > this.timeout;
	}

	// END UTILITY/HELPER METHODS
	// ----------------------------------------------------------------------------------------------------------------
}
