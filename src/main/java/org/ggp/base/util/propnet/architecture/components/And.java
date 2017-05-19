package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The And class is designed to represent logical AND gates.
 */
@SuppressWarnings("serial")
public final class And extends Component
{
	public int counter = 0;
	public boolean useFastMethod = false;

	/**
	 * Returns true if and only if every input to the and is true.
	 *
	 * @see org.ggp.base.util.propnet.architecture.Component#getValue()
	 */
	@Override
	public boolean getValue()
	{
		if (useFastMethod) {
			if (counter == this.numberOfInputs()) return true;
//			if (counter > this.numberOfInputs() || counter < 0) {
//				System.out.println("What the heck did I do wrong this time.");
//			}
			return false;
		} else {
			for ( Component component : getInputs() )
			{
				if ( !component.getValue() )
				{
					return false;
				}
			}
			return true;
		}
	}

	/**
	 * @see org.ggp.base.util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString()
	{
		return toDot("invhouse", "grey", "AND");
	}

}
