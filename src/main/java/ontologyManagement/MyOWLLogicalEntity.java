package ontologyManagement;


import java.util.Set;

import similarity.ComparableElement;


public abstract class MyOWLLogicalEntity implements ComparableElement{
	protected String uri;
	protected MyOWLOntology o;
	protected Set<OWLLink> neighbors;
	
	public void setNeighbors(Set<OWLLink> n)
	{
		neighbors = n;
	}
	
	public Set<OWLLink> getNeighbors()
	{
		return neighbors;
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
		return uri.replaceAll(o.getOntologyPrefix(),"").replace("_",":");//("http://purl.org/obo/owl/GO#", "").replace("_", ":");
	}
	
	public boolean isOWLConcept()
	{
		return o.getOWLConcept(uri) != null;
	}
	
	public OWLConcept getOWLConcept()
	{
		return o.getOWLConcept(uri);
	}
	
	public boolean isMyOWLIndividual()
	{
		return o.getOWLIndividual(uri) != null;
	}
	
	public MyOWLIndividual getOWLIndividual()
	{
		return o.getMyOWLIndividual(uri);
	}
	
	public abstract double taxonomicSimilarity(MyOWLLogicalEntity c) throws Exception;
	protected abstract double similarityNeighbors(MyOWLLogicalEntity c) throws Exception;
}
