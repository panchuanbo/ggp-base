package org.ggp.base.util.propnet.architecture;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * The root class of the Component hierarchy, which is designed to represent
 * nodes in a PropNet. The general contract of derived classes is to override
 * all methods.
 */

public abstract class Component implements Serializable
{

	private static final long serialVersionUID = 352524175700224447L;
    /** The inputs to the component. */
    private final Set<Component> inputs_collection;
    /** The outputs of the component. */
    private final Set<Component> outputs_collection;

    /** The inputs to the component (array) */
    private Component[] inputs;
    /** The outputs of the component. (array) */
    private Component[] outputs;
    /** single input */
    private Component single_input;
    /** single output */
    private Component single_output;

    /** is base? */
    private boolean baseProposition = false;
    /** is input? */
    private boolean inputProposition = false;
    /** is legal? */
    private boolean legalProposition = false;
    /** is goal? */
    private boolean goalProposition = false;

    /** previous value */
    boolean previousValue = false;

    public int componentId = Integer.MIN_VALUE;
    public boolean connectedToTerminal = false;
    public boolean toIgnore = false;

    public void setBase(boolean b) { this.baseProposition = b; }
    public void setInput(boolean b) { this.inputProposition = b; }
    public void setLegal(boolean b) { this.legalProposition = b; }
    public void setGoal(boolean b) { this.goalProposition = b; }
    public boolean isBase() { return this.baseProposition; }
    public boolean isInput() { return this.inputProposition; }
    public boolean isLegal() { return this.legalProposition; }
    public boolean isGoal() { return this.goalProposition; }
    public boolean previousValue() { return this.previousValue; }
    public void setPreviousValue(boolean b) { this.previousValue = b; }
    public int numberOfInputs() { return inputs.length; }
    public int numberOfOutputs() { return outputs.length; }

    /** Whether the value has been calculated or not */
    private boolean calculated;

    /**
     * Creates a new Component with no inputs or outputs.
     */
    public Component()
    {
        this.inputs_collection = new HashSet<Component>();
        this.outputs_collection = new HashSet<Component>();
        this.calculated = false;
    }

    public boolean isCalculated() { return this.calculated; }
    public void setCalculated(boolean b) { this.calculated = b; }

    /**
     * We like arrays
     */
    public void crystalize() {
    	inputs = new Component[this.inputs_collection.size()];
    	outputs = new Component[this.outputs_collection.size()];
    	int index = 0;
    	for (Component c : this.inputs_collection) {
    		if (index == 0) single_input = c;
    		inputs[index] = c;
    		index++;
    	}
    	index = 0;
    	for (Component c : this.outputs_collection) {
    		if (index == 0) single_output = c;
    		outputs[index] = c;
    		index++;
    	}
    }

    /**
     * Adds a new input.
     *
     * @param input
     *            A new input.
     */
    public void addInput(Component input)
    {
        inputs_collection.add(input);
    }

    public void removeInput(Component input)
    {
    	inputs_collection.remove(input);
    }

    public void removeOutput(Component output)
    {
    	outputs_collection.remove(output);
    }

    public void removeAllInputs()
    {
		inputs_collection.clear();
	}

	public void removeAllOutputs()
	{
		outputs_collection.clear();
	}

    /**
     * Adds a new output.
     *
     * @param output
     *            A new output.
     */
    public void addOutput(Component output)
    {
        outputs_collection.add(output);
    }

    /**
     * Getter method.
     *
     * @return The inputs to the component.
     */
    public Set<Component> getInputs()
    {
        return inputs_collection;
    }

    /**
     * A convenience method, to get a single input.
     * To be used only when the component is known to have
     * exactly one input.
     *
     * @return The single input to the component.
     */
    public Component getSingleInput() {
        assert inputs_collection.size() == 1;
        return inputs_collection.iterator().next();
    }

    /**
     * Getter method.
     *
     * @return The outputs of the component.
     */
    public Set<Component> getOutputs()
    {
        return outputs_collection;
    }

    /**
     * A convenience method, to get a single output.
     * To be used only when the component is known to have
     * exactly one output.
     *
     * @return The single output to the component.
     */
    public Component getSingleOutput() {
        assert outputs_collection.size() == 1;
        return outputs_collection.iterator().next();
    }

    /**
     * Getter method.
     *
     * @return The inputs to the component.
     */
    public Component[] fasterGetInputs()
    {
        return inputs;
    }

    /**
     * A convenience method, to get a single input.
     * To be used only when the component is known to have
     * exactly one input.
     *
     * @return The single input to the component.
     */
    public Component fasterGetSingleInput() {
        // assert inputs.length == 1;
        return single_input;
    }

    /**
     * Getter method.
     *
     * @return The outputs of the component.
     */
    public Component[] fasterGetOutputs()
    {
        return this.outputs;
    }

    /**
     * A convenience method, to get a single output.
     * To be used only when the component is known to have
     * exactly one output.
     *
     * @return The single output to the component.
     */
    public Component fasterGetSingleOutput() {
        // assert outputs.length == 1;
        return single_output;
    }

    /**
     * Returns the value of the Component.
     *
     * @return The value of the Component.
     */
    public abstract boolean getValue();

    /**
     * Returns a representation of the Component in .dot format.
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public abstract String toString();

    /**
     * Returns a configurable representation of the Component in .dot format.
     *
     * @param shape
     *            The value to use as the <tt>shape</tt> attribute.
     * @param fillcolor
     *            The value to use as the <tt>fillcolor</tt> attribute.
     * @param label
     *            The value to use as the <tt>label</tt> attribute.
     * @return A representation of the Component in .dot format.
     */
    protected String toDot(String shape, String fillcolor, String label)
    {
        StringBuilder sb = new StringBuilder();

        sb.append("\"@" + Integer.toHexString(hashCode()) + "\"[shape=" + shape + ", style= filled, fillcolor=" + fillcolor + ", label=\"" + label + "\"]; ");
        for ( Component component : getOutputs() )
        {
            sb.append("\"@" + Integer.toHexString(hashCode()) + "\"->" + "\"@" + Integer.toHexString(component.hashCode()) + "\"; ");
        }

        return sb.toString();
    }

}