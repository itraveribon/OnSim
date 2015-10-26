package test;

import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.Locale;

import ontologyManagement.OWLConcept;

public class OWLConceptComparison {
	private OWLConcept conceptA;
	private OWLConcept conceptB;
	private int hash;
	
	public OWLConceptComparison(OWLConcept a, OWLConcept b)
	{
		conceptA = a;
		conceptB = b;
		if (a.getName().compareTo(b.getName()) < 0)
			hash = a.hashCode() ^ b.hashCode();
		else
			hash = b.hashCode() ^ a.hashCode();
	}
	
	public String toString()
	{
		Locale locale  = new Locale("en", "US");
		DecimalFormat formatter = (DecimalFormat) NumberFormat.getNumberInstance(locale);
		formatter.applyPattern("#0.00000000");  
		return conceptA + "\t" + conceptB;
	}
	
	public OWLConcept getConceptA()
	{
		return conceptA;
	}
	
	public OWLConcept getConceptB()
	{
		return conceptB;
	}
	
	public boolean equals(Object o)
	{
		if (o instanceof OWLConceptComparison)
			return equals((OWLConceptComparison) o);
		return false;
	}
	
	public boolean equals(OWLConceptComparison b)
	{
		return conceptA.equals(b.conceptA) && conceptB.equals(b.conceptB) || conceptA.equals(b.conceptB) && conceptB.equals(b.conceptA);
	}
	
	public int hashCode(){
		
		return hash;
	}

}
