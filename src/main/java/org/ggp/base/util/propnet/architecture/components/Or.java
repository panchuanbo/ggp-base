package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Or class is designed to represent logical OR gates.
 */
@SuppressWarnings("serial")
public final class Or extends Component
{
	public int counter = 0;
	public boolean useFastMethod = false;

	/**
	 * Returns true if and only if at least one of the inputs to the or is true.
	 *
	 * @see org.ggp.base.util.propnet.architecture.Component#getValue()
	 */
	@Override
	public boolean getValue()
	{
		if (useFastMethod) {
			if (counter > 0) return true;
			return false;
		} else {
			for ( Component component : getInputs() )
			{
				if ( component.getValue() )
				{
					return true;
				}
			}
			return false;
		}
	}

	/**
	 * @see org.ggp.base.util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString()
	{
		return toDot("ellipse", "grey", "OR");
	}
}