package ontologyManagement;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;

import similarity.ComparableElement;
import similarity.matching.AnnSim;
import similarity.matching.BipartiteGraphMatching;
import similarity.matching.OnJaccard;

public class OWLConcept extends MyOWLLogicalEntity{
	private boolean satisfiable;
	private OWLClass cl;
	private String name;
	
	public OWLConcept(OWLClass a, MyOWLOntology onto)
	{
		o = onto;
		uri = a.getIRI().toURI().toString();
		neighbors = null;
		cl = a;
		name = uri.replaceAll(o.getOntologyPrefix(),"").replace("_",":");
		satisfiable = isSatisfiable();
	}
	
	public OWLClass getOWLClass()
	{
		return cl;
	}
	
	public void setNeighbors(Set<OWLLink> n)
	{
		neighbors = n;
	}
	
	public Set<OWLLink> getNeighbors()
	{
		if (neighbors == null)
			neighbors = o.getConceptOWLLink(this);
		return neighbors;
	}
	
	public void dispose()
	{
		neighbors.clear();
	}
	
	public Set<OWLConcept> getSubConcepts()
	{
		return o.getSubConcepts(this);
	}
	
	public String getURI()
	{
		return uri;
	}
	
	public String toString()
	{
		return uri;
	}
	
	public String getName()
	{
		return name;
	}
	
	public boolean isSatisfiable ()
	{
		return o.isSatisfiable(getOWLClass());
	}
	
	public double similarityNeighbors(OWLConcept c)
	{
		BipartiteGraphMatching bpm = new BipartiteGraphMatching();
		if (neighbors == null)
			neighbors = o.getConceptOWLLink(this);
		if (c.neighbors == null)
			c.neighbors = o.getConceptOWLLink(c);
		try {
			double sim = bpm.matching(neighbors, c.neighbors, this, c);
			return sim;
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return 0.0;
	}
	
	public double taxonomicSimilarity(OWLConcept c)
	{
		return o.taxonomicClassSimilarity(this, c);
	}
	
	public double taxonomicSimilarity(MyOWLLogicalEntity c) throws Exception
	{
		if (!(c instanceof OWLConcept))
				throw new Exception("Invalid comparison between " + this + " and " + c);
		return taxonomicSimilarity((OWLConcept)c);	
	}
	
	public boolean isSubConceptOf(OWLConcept c)
	{
		return o.isSubClassOf(getOWLClass(), c.getOWLClass());
	}
	
	/*public double getIC()
	{
		InformationContent ic;
		Double res = null;
		try {
			ic = InformationContent.getInstance();
			res = ic.getIC(this);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return res;
	}
	
	public double similarityIC(OWLConcept c)
	{
		double informC = 0;
		try {
			OWLConcept lca = this.getLCA(c);
			InformationContent ic = InformationContent.getInstance();
			informC = ic.getIC(lca);
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return informC;
	}
	
	public double similarityDCA(OWLConcept c)
	{
		double informC = 0;
		try {
			Set<OWLConcept> dca = o.getDCA(this, c);
			for (OWLConcept con: dca)
			{
				informC += con.getIC();
			}
			informC = informC / dca.size();
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return informC;
	}
	
	public double similarityMICA(OWLConcept c)
	{
		double informC = 0;
		try {
			Set<OWLConcept> cA = o.getAncestors(this);
			Set<OWLConcept> cB = o.getAncestors(c);
			cA.retainAll(cB);
			InformationContent ic = InformationContent.getInstance();
			for (OWLConcept con: cA)
			{
				if (ic.getIC(con) > informC)
					informC = ic.getIC(con);
			}
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return informC;
	}
	*/
	public double getDepth()
	{
		getOWLClass();
		return o.prof(this.cl);
	}
	
	public double similarity(OWLConcept c)
	{
		if (!satisfiable || !c.satisfiable)
			return 0;

		
		
		if (this == c)
			return 1.0;//(2.0 + informC)/3;
		
		//double informC = similarityDCA(c);
		//double informC = similarityIC(c);
		double taxSim = taxonomicSimilarity(c);
		Double sim = taxSim;
		double neighSim = 1;
		if (taxSim > 0 )
		{
			/*if (this.neighbors.isEmpty() && c.neighbors.isEmpty())
				neighSim = informC;
			else*/
				neighSim = similarityNeighbors(c);
		}
			

		sim = taxSim * neighSim;
		//sim = sim*informC + 0.0;//(sim + informC)/2;
		
		return sim;
	}
	public double similarity(ComparableElement a, MyOWLLogicalEntity org, MyOWLLogicalEntity des) throws Exception {
		if (!(a instanceof OWLConcept))
			throw new Exception("Invalid comparison between " + this + " and " + a);
		return similarity((OWLConcept)a);
	}
	
	public OWLConcept getLCA(OWLConcept b)
	{
		return o.getLCS(this, b);
	}

	@Override
	protected double similarityNeighbors(MyOWLLogicalEntity c) throws Exception {
		if (!(c instanceof OWLConcept))
			throw new Exception("Invalid comparison between " + this + " and " + c);
		return similarityNeighbors((OWLConcept)c);
	}

}
