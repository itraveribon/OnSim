package ontologyManagement;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.mindswap.pellet.KnowledgeBase;
import org.mindswap.pellet.utils.ATermUtils;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;

import aterm.ATermAppl;

import com.clarkparsia.pellet.owlapiv3.PelletReasoner;

public class SparQLDL {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		String ontFile = "/home/traverso/Downloads/CESSM/explanationExample1.owl";
		MyOWLOntology o = new MyOWLOntology(ontFile);
		
		OWLConcept a = o.getOWLConcept("http://www.semanticweb.org/traverso/ontologies/2014/11/untitled-ontology-296#E");
		OWLConcept b = o.getOWLConcept("http://www.semanticweb.org/traverso/ontologies/2014/11/untitled-ontology-296#F");
		PelletReasoner reasoner = new PelletReasoner(o.getOWLOntology(),null);
		reasoner.prepareReasoner();
		System.out.println(reasoner.getSuperClasses(a.getOWLClass(), false));
		Set<OWLLink> neighborsA = new HashSet<OWLLink>();
		Set<OWLClassExpression> superClasses = a.getOWLClass().getSuperClasses(o.getOWLOntology());
		Set<OWLObjectSomeValuesFrom> someValues = new HashSet<OWLObjectSomeValuesFrom>();
		for (Iterator<OWLClassExpression> i = superClasses.iterator(); i.hasNext();)
		{
			OWLClassExpression c = i.next();
			if (c.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
			{
				OWLObjectSomeValuesFrom aux = (OWLObjectSomeValuesFrom) c;
				someValues.add(aux);
				OWLObjectProperty p = aux.getProperty().asOWLObjectProperty();
				OWLClass destiny = aux.getFiller().asOWLClass();
				Set<OWLObjectPropertyExpression> superProperties = reasoner.getSuperObjectProperties(p, false).getFlattened();
				for (Iterator<OWLObjectPropertyExpression> j = superProperties.iterator(); j.hasNext();)
				{
					OWLObjectProperty auxProperty = j.next().asOWLObjectProperty();
					neighborsA.add(new OWLLink(o.getOWLObjectProperty(auxProperty.toStringID()), o.getOWLConcept(destiny.toStringID())));
				}
			}
		}
	}
	
	public static Set<OWLLink> getNeighbors(OWLConcept c)
	{
		
	}

}
