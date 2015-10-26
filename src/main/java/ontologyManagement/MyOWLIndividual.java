package ontologyManagement;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;

import similarity.ComparableElement;
import similarity.InformationContent;
import similarity.matching.BipartiteGraphMatching;


public class MyOWLIndividual extends MyOWLLogicalEntity{
	private OWLNamedIndividual ind;
	private Map<MyOWLIndividual, Double> ownSimilarities;
	private static Map<MyOWLIndividual,Map<MyOWLIndividual, Double>> similarities = new HashMap<MyOWLIndividual,Map<MyOWLIndividual, Double>>();
	
	public MyOWLIndividual(OWLNamedIndividual a, MyOWLOntology onto)
	{
		o = onto;
		uri = a.getIRI().toURI().toString();
		neighbors = null;
		ind = a;
		ownSimilarities = new HashMap<MyOWLIndividual,Double>();
		similarities.put(this, ownSimilarities);
	}
	
	public OWLNamedIndividual getOWLNamedIndividual()
	{
		if (ind == null)
			ind = o.getOWLIndividual(uri).asOWLNamedIndividual();
		return ind;
	}
	
	
	private double similarityNeighbors(MyOWLIndividual c)
	{
		BipartiteGraphMatching bpm = new BipartiteGraphMatching();
		if (neighbors == null)
			neighbors = o.getIndividualOWLLink(this);
		if (c.neighbors == null)
			c.neighbors = o.getIndividualOWLLink(c);
		try {
			double sim = bpm.matching(neighbors, c.neighbors, this, c);
			return sim;
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return 0.0;
	}
	
	@Override
	protected double similarityNeighbors(MyOWLLogicalEntity c) throws Exception{
		if (c instanceof MyOWLIndividual)
		{
			MyOWLIndividual ind = (MyOWLIndividual) c;
			return this.similarityNeighbors(ind);
		}
		return 0;
	}
	
	public double taxonomicSimilarity(MyOWLIndividual c)
	{
		return o.taxonomicIndividualSimilarity(getOWLNamedIndividual(), c.getOWLNamedIndividual());
	}
	
	public double taxonomicSimilarity(MyOWLLogicalEntity c) throws Exception
	{
		if (!(c instanceof MyOWLIndividual))
				throw new Exception("Invalid comparison between " + this + " and " + c);
		return taxonomicSimilarity((MyOWLIndividual)c);	
	}
	
	public boolean isOfType(OWLConcept c)
	{
		return o.isOfType(getOWLNamedIndividual(), c.getOWLClass());
	}
	
	public double getIC()
	{
		return 1;
	}
	
	public double getDepth()
	{
		return o.prof(this.ind);
	}
	
	public double similarity(MyOWLIndividual c)
	{
		if (this == c)
			return 1.0;
		Double sim = ownSimilarities.get(c);
		if (sim != null)
			return sim;
		
		double taxSim = taxonomicSimilarity(c);
		double neighSim = 1;
		if (taxSim > 0)
			neighSim = similarityNeighbors(c);
		//System.out.println(this + "\t" + c + "\t" + taxSim + "\t" + neighSim);
		//System.out.println(this + "\t" + c + "\t" + taxSim + "\t" + taxSim*neighSim);
		sim = taxSim*neighSim;
		ownSimilarities.put(c, sim);
		c.ownSimilarities.put(this, sim);
		return sim;
	}
	public double similarity(ComparableElement a, MyOWLIndividual org, MyOWLIndividual des) throws Exception {
		if (!(a instanceof OWLConcept))
			throw new Exception("Invalid comparison between " + this + " and " + a);
		return similarity((MyOWLIndividual)a);
	}
	
	public OWLConcept getLCA(MyOWLIndividual b)
	{
		return o.getLCS(this, b);
	}

	public double similarity(ComparableElement a, MyOWLLogicalEntity org, MyOWLLogicalEntity des)
			throws Exception {
		if (!(a instanceof MyOWLIndividual))
			throw new Exception("Invalid comparison between " + this + " and " + a);
		return similarity((MyOWLIndividual)a);
	}
}
