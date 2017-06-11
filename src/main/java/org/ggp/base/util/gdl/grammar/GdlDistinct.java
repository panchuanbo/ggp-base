package org.ggp.base.util.gdl.grammar;

@SuppressWarnings("serial")
public final class GdlDistinct extends GdlLiteral
{

	private final GdlTerm arg1;
	private final GdlTerm arg2;
	private transient Boolean ground;

	GdlDistinct(GdlTerm arg1, GdlTerm arg2)
	{
		this.arg1 = arg1;
		this.arg2 = arg2;
		ground = null;
	}

	public GdlTerm getArg1()
	{
		return arg1;
	}

	public GdlTerm getArg2()
	{
		return arg2;
	}

	@Override
	public boolean isGround()
	{
		if (ground == null)
		{
			ground = arg1.isGround() && arg2.isGround();
		}

		return ground;
	}

	@Override
	public String toString()
	{
		return "( distinct " + arg1 + " " + arg2 + " )";
	}

	@Override
	public String infixString() {
		return "distinct(" + arg1.infixString() + "," + arg2.infixString() + ")";
	}

	@Override
	public String toASPString() {
		return "not " + arg1.toASPString() + "=" + arg2.toASPString();
	}

}
