package ontologyManagement;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import kse.findj.edg.core.ExplanationRoutine;
import kse.findj.edg.core.MasterRoutine;
import kse.findj.edg.core.MyAxiomRecorder;
import kse.findj.edg.data.AxiomGCI0;
import kse.findj.edg.data.AxiomGCI1;
import kse.findj.edg.data.AxiomGCI2;
import kse.findj.edg.data.AxiomGCI3;
import kse.findj.edg.data.AxiomR;
import kse.findj.edg.data.AxiomRI2;
import kse.findj.edg.data.AxiomRI3;
import kse.findj.edg.data.AxiomS;
import kse.findj.edg.data.MyAxiom;
import kse.findj.edg.data.MyAxiomRepository;
import kse.findj.reasoner.ELKOWLOntologyReasoner;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Configuration.TableauMonitorType;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.elk.owlapi.ElkReasoner;
import org.semanticweb.elk.owlapi.ElkReasonerConfiguration;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorFactory;
import org.semanticweb.owl.explanation.api.ExplanationManager;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLLogicalEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.PrefixManager;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.reasoner.TimedConsoleProgressMonitor;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasoner;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasonerFactory;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import test.ComparisonResult;
import test.DatasetTest;
import test.OWLConceptComparison;

import com.clarkparsia.owlapi.explanation.DefaultExplanationGenerator;
import com.clarkparsia.owlapi.explanation.util.ExplanationProgressMonitor;
import com.clarkparsia.owlapi.explanation.util.SilentExplanationProgressMonitor;

public class MyOWLOntology {
	private OWLOntologyManager manager;
	private OWLOntology o;
	private Map<String, OWLConcept> concepts;
	private Map<OWLClass, Set<OWLClass>> ancestors;
	private Map<String, MyOWLIndividual> individuals;
	private Map<OWLClass, Map<OWLClass, Integer>> conceptDistances;
	private Map<String, OWLRelation> relations;
	private OWLReasoner reasoner;
	private ELKOWLOntologyReasoner reasonerExpl;
	private OWLDataFactory factory;
	private ExplanationGenerator<OWLAxiom> expl;
	private String prefix;
	private Map<OWLRelation, Set<List<OWLRelation>>> propertyChains;
	private MyAxiomRepository repository;
	private int expID;
	private Map<OWLConceptComparison, OWLConcept> lcas;
	private Map<OWLConceptComparison, Set<OWLConcept>> disAncestors;
	private static int equivalentClassNumber = 0;
	private Set<OWLConcept> roots;
	private HashMap<OWLClass, Integer> conceptProfs = new HashMap<OWLClass,Integer>();
	private HashMap<OWLObjectProperty, Integer> relationProfs = new HashMap<OWLObjectProperty,Integer>();
	private boolean storing = true;
	
	public MyOWLOntology(String ontFile, String pr)
	{
		concepts = new HashMap<String,OWLConcept>();
		individuals = new HashMap<String, MyOWLIndividual>();
		relations = new HashMap<String,OWLRelation>();
		ancestors = new HashMap<OWLClass, Set<OWLClass>>();
		manager = OWLManager.createOWLOntologyManager();
		factory = manager.getOWLDataFactory();
		conceptDistances = new HashMap<OWLClass, Map<OWLClass, Integer>>();
		prefix = pr;
		lcas = new HashMap<OWLConceptComparison, OWLConcept>();
		disAncestors = new HashMap<OWLConceptComparison, Set<OWLConcept>>();
    	expID = 0;
		
		try {
			o = manager.loadOntologyFromOntologyDocument(new File(ontFile));
			System.out.println("GOOOOL");
			startReasoner();
            System.out.println("Reasoner ready");			
			Set<OWLObjectProperty> objectProperties = o.getObjectPropertiesInSignature();
			objectProperties.remove(factory.getOWLTopObjectProperty());
			for (Iterator<OWLObjectProperty> i = objectProperties.iterator(); i.hasNext();)
			{
				OWLObjectProperty current = i.next();
				relations.put(current.toStringID(), new OWLRelation(current, this));
			}
			
			System.out.println("Relations read");
			
			Set<OWLClass> classes = o.getClassesInSignature();
			classes.add(factory.getOWLThing());
			for (Iterator<OWLClass> i = classes.iterator(); i.hasNext();)
			{
				OWLClass current = i.next();
				concepts.put(current.toStringID(), new OWLConcept(current, this));
			}
			classes = null; //Finished with classes
			System.out.println("Classes read");

            Set<OWLNamedIndividual> indivs = o.getIndividualsInSignature();
            for (Iterator<OWLNamedIndividual> i = indivs.iterator(); i.hasNext();)
            {
            	OWLNamedIndividual current = i.next();
            	individuals.put(current.toStringID(), new MyOWLIndividual(current, this));
            }
            
            /*roots = new HashSet<OWLConcept>();
            roots.add(concepts.get(factory.getOWLThing().toStringID()));
            roots.add(concepts.get(this.getOntologyPrefix() + "GO_0008150"));
            roots.add(concepts.get(this.getOntologyPrefix() + "GO_0005575"));
            roots.add(concepts.get(this.getOntologyPrefix() + "GO_0003674"));*/
		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		propertyChains = this.getPropertyChains();
	}
	
	public OWLOntology getOWLOntology()
	{
		return o;
	}
	
	public String getOntologyPrefix()
	{
		return prefix;
	}
	
	public Set<OWLRelation> getOWLRelations()
	{
		return new HashSet<OWLRelation>(relations.values());
	}
	
	public Set<OWLLink> getConceptOWLLink (OWLConcept c)
	{
		Set<OWLLink> ownLinks = new HashSet<OWLLink>();
		Set<OWLConcept> potentialNeighbors = getIsland(c);
		if (reasoner instanceof Reasoner)
		{
			for (Iterator<OWLConcept> j = potentialNeighbors.iterator(); j.hasNext();)
			{
				OWLConcept d = j.next();
				for (Iterator<OWLRelation> k = relations.values().iterator(); k.hasNext();)
				{
					OWLRelation r = k.next();
					Set<OWLExplanation> exps = checkOWLLink(c, r, d); 
					if (exps != null)
					{
						OWLLink link = new OWLLink(r, d, exps); //All the links, inferred and not inferred, have explanations
						ownLinks.add(link);
					}
				}
			}
		}
		else if (reasoner instanceof ElkReasoner)
			ownLinks = getConceptOWLLinks(c, potentialNeighbors);
		return ownLinks;
	}
	
	public void setOWLLinks (Set<OWLConcept> concepts)
	{
		Map<OWLConcept, Map<OWLClass, OWLAxiom>> axioms = new HashMap<OWLConcept, Map<OWLClass, OWLAxiom>>();
		
		for (Iterator<OWLConcept> i = concepts.iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			Set<OWLConcept> potentialNeighbors = getIsland(c);
			Map<OWLClass, OWLAxiom> register = addEquivalentAxioms(c, potentialNeighbors);
			axioms.put(c, register);
		}
		reasoner.flush();
		for (Iterator<OWLConcept> i = axioms.keySet().iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			OWLClass a = c.getOWLClass();
			Map<OWLClass, OWLAxiom> register = axioms.get(c);
			Set<OWLLink> links = new HashSet<OWLLink>();
			for (Iterator<OWLClass> j = register.keySet().iterator(); j.hasNext();)
			{
				OWLClass test = j.next();
				OWLSubClassOfAxiom expression = (OWLSubClassOfAxiom) register.get(test);
				links.addAll(confirmedLinks(a, test, expression));
			}
			c.setNeighbors(links);
		}
		
		fullExplanations(axioms.keySet());

		for (Iterator<OWLConcept> i = axioms.keySet().iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			Map<OWLClass, OWLAxiom> register = axioms.get(c);
			for (Iterator<OWLClass> j = register.keySet().iterator(); j.hasNext();)
			{
				OWLClass test = j.next();
				OWLAxiom expression = register.get(test);
				manager.removeAxiom(o, expression);
			}
		}
		reasoner.flush();
	}
	
	private void fullExplanations(Set<OWLConcept> axioms)
	{
		Map<OWLSubClassOfAxiom, OWLLink> mapAxioms = new HashMap<OWLSubClassOfAxiom, OWLLink>();
		for (Iterator<OWLConcept> i = axioms.iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			for (OWLLink l: c.getNeighbors())
			{
				OWLSubClassOfAxiom linkAxiom = buildAxiom(l.getRelation().getOWLObjectProperty(), c.getOWLClass(), l.getDestiny().getOWLConcept().getOWLClass());
				mapAxioms.put(linkAxiom, l);
			}
		}
		Map<OWLSubClassOfAxiom, Set<OWLExplanation>> explanations = getQuickExplanations(mapAxioms.keySet());
		for (OWLSubClassOfAxiom ax: explanations.keySet())
		{
			mapAxioms.get(ax).setExplanations(explanations.get(ax));
		}
	}
	
	
	//This function returns only the links entailed in the ontology. The explanations are not computed at this time
	private Set<OWLLink> confirmedLinks(OWLClass a, OWLClass test, OWLSubClassOfAxiom expression)
	{
		Set<OWLLink> links = new HashSet<OWLLink>();
		if (reasoner instanceof ElkReasoner)
		{
			if (!reasoner.isSatisfiable(test))
			{
				OWLObjectIntersectionOf intersection = (OWLObjectIntersectionOf) expression.getSuperClass();
				Set<OWLClassExpression> interSet = intersection.asConjunctSet();
				interSet.remove(a);
				OWLObjectComplementOf negation = (OWLObjectComplementOf) interSet.iterator().next();
				OWLObjectSomeValuesFrom exp = (OWLObjectSomeValuesFrom) negation.getOperand();
				OWLRelation r = this.getOWLRelation(exp.getProperty().asOWLObjectProperty().toStringID());
				OWLConcept d = this.getOWLConcept(exp.getFiller().asOWLClass().toStringID());
				//OWLObjectSomeValuesFrom relationAxiom = factory.getOWLObjectSomeValuesFrom(r.getOWLObjectProperty(), d.getOWLClass());
				//OWLSubClassOfAxiom linkAxiom = factory.getOWLSubClassOfAxiom(a, relationAxiom);
				OWLLink link = new OWLLink(r, d);//, getQuickExplanations(linkAxiom));
				links.add(link);
			}
		}
		else if (reasoner instanceof Reasoner)
		{
			OWLObjectIntersectionOf intersection = (OWLObjectIntersectionOf) expression.getSuperClass(); //aux.iterator().next();
			Set<OWLClassExpression> interSet = intersection.asConjunctSet();
			interSet.remove(a);
			OWLObjectComplementOf negation = (OWLObjectComplementOf) interSet.iterator().next();
			OWLObjectSomeValuesFrom exp = (OWLObjectSomeValuesFrom) negation.getOperand();
			OWLRelation r = this.getOWLRelation(exp.getProperty().asOWLObjectProperty().toStringID());
			OWLConcept d = this.getOWLConcept(exp.getFiller().asOWLClass().toStringID());
			OWLObjectSomeValuesFrom relationAxiom = factory.getOWLObjectSomeValuesFrom(r.getOWLObjectProperty(), d.getOWLClass());
			OWLSubClassOfAxiom linkAxiom = factory.getOWLSubClassOfAxiom(a, relationAxiom);
			if (reasoner.isEntailed(linkAxiom))
			{
				OWLLink link = new OWLLink(r, d);//, getExplanations(linkAxiom));
				links.add(link);
			}
		}
		return links;
	}
	
	public Map<OWLClass, OWLAxiom> addEquivalentAxioms(OWLConcept c, Set<OWLConcept> potentialNeighbors)
	{
		Map<OWLClass, OWLAxiom> register = new HashMap<OWLClass, OWLAxiom>();
		OWLClass a = c.getOWLClass();
		PrefixManager pm = new DefaultPrefixManager(prefix);
		for (Iterator<OWLConcept> j = potentialNeighbors.iterator(); j.hasNext();)
		{
			OWLConcept d = j.next();
			OWLClass b = d.getOWLClass();
			for (Iterator<OWLRelation> k = relations.values().iterator(); k.hasNext();)
			{
				OWLRelation r = k.next();
				OWLObjectProperty p = r.getOWLObjectProperty();
				OWLObjectSomeValuesFrom relationAxiom = factory.getOWLObjectSomeValuesFrom(p, b);
				OWLClassExpression negation = factory.getOWLObjectComplementOf(relationAxiom);
		        Set<OWLClassExpression> intersection = new HashSet<OWLClassExpression>();
		        intersection.add(a);
		        intersection.add(negation);
		        OWLObjectIntersectionOf intersectionAxiom = factory.getOWLObjectIntersectionOf(intersection);
		        OWLClass test = factory.getOWLClass(":test" + equivalentClassNumber, pm);
		        equivalentClassNumber++;
		        OWLAxiom definition = factory.getOWLSubClassOfAxiom(test, intersectionAxiom);//.getOWLEquivalentClassesAxiom(test, intersectionAxiom);
		        register.put(test, definition);
			}
		}
		manager.addAxioms(o, new HashSet<OWLAxiom>(register.values()));
		return register;
	}
	
	
	public Set<OWLLink> getConceptOWLLinks (OWLConcept c, Set<OWLConcept> potentialNeighbors)
	{
		Set<OWLLink> links = new HashSet<OWLLink>();
		OWLClass a = c.getOWLClass();
		Map<OWLClass, OWLAxiom> register = addEquivalentAxioms(c, potentialNeighbors);
		
		reasoner.flush();
		for (Iterator<OWLClass> i = register.keySet().iterator(); i.hasNext();)
		{
			OWLClass test = i.next();
			OWLSubClassOfAxiom expression = (OWLSubClassOfAxiom) register.get(test);
			links.addAll(confirmedLinks(a, test, expression));
		}
		manager.removeAxioms(o, new HashSet<OWLAxiom>(register.values()));
		return links;
	}
	
	private OWLSubClassOfAxiom buildAxiom (OWLObjectProperty p, OWLClass origin, OWLClass destiny)
	{
		//====================BUILD AXIOM=================================
        OWLObjectSomeValuesFrom relationAxiom = factory.getOWLObjectSomeValuesFrom(p, destiny);
        OWLSubClassOfAxiom linkAxiom = factory.getOWLSubClassOfAxiom(origin, relationAxiom);
        return linkAxiom;
        //============== END BUILDING AXIOM ================================
	}
	
	private Map<OWLSubClassOfAxiom, Set<OWLExplanation>> getExplanations (Set<OWLSubClassOfAxiom> linkAxioms)
	{
		Map<OWLSubClassOfAxiom, Set<OWLExplanation>> mapExpl = new HashMap<OWLSubClassOfAxiom, Set<OWLExplanation>>();
		for (OWLSubClassOfAxiom linkAxiom: linkAxioms)
		{
			if (o.containsAxiom(linkAxiom))
	        {
	        	mapExpl.put(linkAxiom, new HashSet<OWLExplanation>());
	        }
			else
				mapExpl.put(linkAxiom, getExplanations(linkAxiom));
		}
		return mapExpl;
	}
	
	private Set<OWLExplanation> getExplanations (OWLSubClassOfAxiom linkAxiom)
	{
		//============== GETTING EXPLANATION ===============================
        Set<OWLExplanation> explanations = null;
        if (o.containsAxiom(linkAxiom))
        {
        	explanations = Collections.emptySet();
        }
        else
        {
        	explanations = new HashSet<OWLExplanation>();
        	Set<Explanation<OWLAxiom>> expAxioms = expl.getExplanations(linkAxiom, 1);
        	for (Iterator<Explanation<OWLAxiom>> j = expAxioms.iterator(); j.hasNext();)
        	{
        		OWLExplanation e;
				try {
					e = new OWLExplanation(j.next().getAxioms(), this);
					explanations.add(e);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
        	}
        }
        return explanations;
        //============= END GETTING EXPLANATION ===============================
	}
	
	private Map<OWLSubClassOfAxiom, Set<OWLExplanation>> getQuickExplanations (Set<OWLSubClassOfAxiom> linkAxioms)
	{
		Map<OWLSubClassOfAxiom, Set<OWLExplanation>> mapExpl = new HashMap<OWLSubClassOfAxiom, Set<OWLExplanation>>();
		Map<OWLSubClassOfAxiom, OWLAxiom> mapJust = new HashMap<OWLSubClassOfAxiom, OWLAxiom>();
		for (OWLSubClassOfAxiom linkAxiom: linkAxioms)
		{
			if (o.containsAxiom(linkAxiom))
	        {
	        	mapExpl.put(linkAxiom, new HashSet<OWLExplanation>());
	        }
	        else
	        {
	        	OWLClass a = linkAxiom.getSubClass().asOWLClass();
	        	OWLObjectSomeValuesFrom relationAxiom = (OWLObjectSomeValuesFrom) linkAxiom.getSuperClass();
	        	
	        	PrefixManager pm = new DefaultPrefixManager(prefix);
	    		OWLClass test = factory.getOWLClass(":testExpl" + expID++, pm);
	    		Set<OWLClassExpression> equivalents = new HashSet<OWLClassExpression>();
	    		equivalents.add(test);
	    		equivalents.add(relationAxiom);
	    		OWLSubClassOfAxiom equiv = factory.getOWLSubClassOfAxiom(relationAxiom, test);
	    		mapJust.put(linkAxiom, equiv);
	        }
		}
		//manager.addAxioms(o, new HashSet<OWLAxiom>(mapJust.values()));
		//reasonerExpl.flush(repository);
		reasonerExpl.flush(repository, new HashSet<OWLAxiom>(mapJust.values()));
		
		for (OWLSubClassOfAxiom l: mapJust.keySet())
		{
			OWLClass a = l.getSubClass().asOWLClass();
			OWLClass test = ((OWLSubClassOfAxiom) mapJust.get(l)).getSuperClass().asOWLClass();
			
			int threadNum = 1;
    		MasterRoutine masterRoutine = new MasterRoutine(repository, threadNum, reasonerExpl.getIntegerClass(a.toStringID()), reasonerExpl.getIntegerClass(test.toStringID()));//.toStringID()));		
    		masterRoutine.computeResult();
    		
    		Set<ExplanationRoutine> justifications = masterRoutine.getJustifications();
    		MyAxiomRecorder recorder = masterRoutine.getRecorder();
    		Map<Integer, OWLClass> classMap = reasonerExpl.getClassMap();
    		Map<Integer, OWLObjectProperty> propMap = reasonerExpl.getObjectPropertyMap();
    		Set<Set<OWLAxiom>> axiomsSets = new HashSet<Set<OWLAxiom>>();
    		//boolean noExpl = false;
    		//for (Iterator<ExplanationRoutine> i = justifications.iterator(); i.hasNext(); )
    		for(ExplanationRoutine expRoutine : justifications){
    			//ExplanationRoutine expRoutine = i.next();
    			Set<Integer> justs = expRoutine.getOriginalAxioms();
    			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
    			boolean addExplanation = true;
    			//for(Integer just : justs){
    			for (Iterator<Integer> j = justs.iterator(); j.hasNext() && addExplanation; ){
    				Integer just = j.next();
    				MyAxiom ax = recorder.getAxiomFromId(just);
    				OWLAxiom axiom = null;
    				if (ax instanceof AxiomGCI0)
    				{
    					AxiomGCI0 gci0 = (AxiomGCI0) ax;
    					axiom = factory.getOWLSubClassOfAxiom(classMap.get(gci0.getSubClass()), classMap.get(gci0.getSuperClass()));
    				}
    				else if (ax instanceof AxiomGCI1)
    				{
    					AxiomGCI1 gci1 = (AxiomGCI1) ax;
    					OWLClass x = classMap.get(gci1.getLeftSubClass());
    					OWLClass y = classMap.get(gci1.getRightSubClass());
    					OWLClass sup = classMap.get(gci1.getSuperClass());
    					Set<OWLClass> intersection = new HashSet<OWLClass>();
    					intersection.add(x);
    					intersection.add(y);
    					if (x == null || y == null)
    						addExplanation = false;
    					else
    					{
    						OWLClassExpression interAx = factory.getOWLObjectIntersectionOf(intersection);
    						axiom = factory.getOWLSubClassOfAxiom(interAx, sup);
    					}
    				}
    				else if (ax instanceof AxiomGCI2)
    				{
    					AxiomGCI2 gci2 = (AxiomGCI2) ax;
    					OWLClass x = classMap.get(gci2.getSubClass());
    					OWLClass y = classMap.get(gci2.getClassInSuperClass());
    					OWLObjectProperty prop = propMap.get(gci2.getPropertyInSuperClass());
    					OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, y);
    					axiom = factory.getOWLSubClassOfAxiom(x, e);
    				}
    				else if (ax instanceof AxiomGCI3)
    				{
    					AxiomGCI3 gci3 = (AxiomGCI3) ax;
    					OWLClass x = classMap.get(gci3.getClassInSubClass());
    					OWLClass y = classMap.get(gci3.getSuperClass());
    					OWLObjectProperty prop = propMap.get(gci3.getPropertyInSubClass());
    					if (x == null || y == null || prop == null)
    						addExplanation = false;
    					else
    					{
    						OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, x);
    						axiom = factory.getOWLSubClassOfAxiom(e, y);
    					}
    				}
    				else if (ax instanceof AxiomRI2)
    				{
    					AxiomRI2 ri2 = (AxiomRI2) ax;
    					OWLObjectProperty x = propMap.get(ri2.getSubProperty());
    					OWLObjectProperty y = propMap.get(ri2.getSuperProperty());
    					axiom = factory.getOWLSubObjectPropertyOfAxiom(x, y);
    				}
    				else if (ax instanceof AxiomRI3)
    				{
    					AxiomRI3 ri3 = (AxiomRI3) ax;
    					OWLObjectProperty x = propMap.get(ri3.getLeftSubProperty());
    					OWLObjectProperty y = propMap.get(ri3.getRightSubProperty());
    					OWLObjectProperty z = propMap.get(ri3.getSuperProperty());
    					List<OWLObjectProperty> chain = new ArrayList<OWLObjectProperty>();
    					chain.add(x);
    					chain.add(y);
    					axiom = factory.getOWLSubPropertyChainOfAxiom(chain, z);
    				}
    				else if (ax instanceof AxiomR)
    				{
    					AxiomR r = (AxiomR) ax;
    					OWLClass x = classMap.get(r.getSubClass());
    					OWLClass y = classMap.get(r.getClassInSuperClass());
    					OWLObjectProperty prop = propMap.get(r.getPropertyInSuperClass());
    					OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, y);
    					axiom = factory.getOWLSubClassOfAxiom(x, e);
    				}
    				else if (ax instanceof AxiomS)
    				{
    					AxiomS s = (AxiomS) ax;
    					OWLClass x = classMap.get(s.getSubClass());
    					OWLClass y = classMap.get(s.getSuperClass());
    					axiom = factory.getOWLSubClassOfAxiom(x, y);
    				}
    				if (axiom != null && !axiom.getClassesInSignature().contains(test))
    				{
    					axioms.add(axiom);
    				}
    			}
    			if (addExplanation)
    				axiomsSets.add(axioms);
    		}
    		
    		Set<OWLExplanation> explanations = new HashSet<OWLExplanation>();
    		int i = 0;
        	for (Iterator<Set<OWLAxiom>> j = axiomsSets.iterator(); j.hasNext() && i < 1; i++)
        	{
        		OWLExplanation e;
				try {
					e = new OWLExplanation(j.next(), this);
					explanations.add(e);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
        	}
        	mapExpl.put(l, explanations);
        }
        
		manager.removeAxioms(o, new HashSet<OWLAxiom>(mapJust.values()));
		reasoner.flush();
		return mapExpl;
	}
	
	private Set<OWLExplanation> getQuickExplanations (OWLSubClassOfAxiom linkAxiom)
	{
		//============== GETTING EXPLANATION ===============================
        Set<OWLExplanation> explanations = null;
        if (o.containsAxiom(linkAxiom))
        {
        	explanations = Collections.emptySet();
        }
        else
        {
        	OWLClass a = linkAxiom.getSubClass().asOWLClass();
        	OWLObjectSomeValuesFrom relationAxiom = (OWLObjectSomeValuesFrom) linkAxiom.getSuperClass();
        	
        	PrefixManager pm = new DefaultPrefixManager(prefix);
    		OWLClass test = factory.getOWLClass(":testExpl" + expID++, pm);
    		Set<OWLClassExpression> equivalents = new HashSet<OWLClassExpression>();
    		equivalents.add(test);
    		equivalents.add(relationAxiom);
    		OWLSubClassOfAxiom equiv = factory.getOWLSubClassOfAxiom(relationAxiom, test);
    		manager.addAxiom(o, equiv);
    		
    		reasonerExpl.flush(repository); 
            
    		
    		
    		int threadNum = 1;
    		MasterRoutine masterRoutine = new MasterRoutine(repository, threadNum, reasonerExpl.getIntegerClass(a.toStringID()), reasonerExpl.getIntegerClass(test.toStringID()));//.toStringID()));		
    		masterRoutine.computeResult();
    		
    		Set<ExplanationRoutine> justifications = masterRoutine.getJustifications();
    		MyAxiomRecorder recorder = masterRoutine.getRecorder();
    		Map<Integer, OWLClass> classMap = reasonerExpl.getClassMap();
    		Map<Integer, OWLObjectProperty> propMap = reasonerExpl.getObjectPropertyMap();
    		Set<Set<OWLAxiom>> axiomsSets = new HashSet<Set<OWLAxiom>>();
    		for(ExplanationRoutine expRoutine : justifications){
    			Set<Integer> justs = expRoutine.getOriginalAxioms();
    			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
    			for(Integer just : justs){
    				MyAxiom ax = recorder.getAxiomFromId(just);
    				OWLAxiom axiom = null;
    				if (ax instanceof AxiomGCI0)
    				{
    					AxiomGCI0 gci0 = (AxiomGCI0) ax;
    					axiom = factory.getOWLSubClassOfAxiom(classMap.get(gci0.getSubClass()), classMap.get(gci0.getSuperClass()));
    				}
    				else if (ax instanceof AxiomGCI1)
    				{
    					AxiomGCI1 gci1 = (AxiomGCI1) ax;
    					OWLClass x = classMap.get(gci1.getLeftSubClass());
    					OWLClass y = classMap.get(gci1.getRightSubClass());
    					OWLClass sup = classMap.get(gci1.getSuperClass());
    					Set<OWLClass> intersection = new HashSet<OWLClass>();
    					intersection.add(x);
    					intersection.add(y);
    					OWLClassExpression interAx = factory.getOWLObjectIntersectionOf(intersection);
    					axiom = factory.getOWLSubClassOfAxiom(interAx, sup);
    				}
    				else if (ax instanceof AxiomGCI2)
    				{
    					AxiomGCI2 gci2 = (AxiomGCI2) ax;
    					OWLClass x = classMap.get(gci2.getSubClass());
    					OWLClass y = classMap.get(gci2.getClassInSuperClass());
    					OWLObjectProperty prop = propMap.get(gci2.getPropertyInSuperClass());
    					OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, y);
    					axiom = factory.getOWLSubClassOfAxiom(x, e);
    				}
    				else if (ax instanceof AxiomGCI3)
    				{
    					AxiomGCI3 gci3 = (AxiomGCI3) ax;
    					OWLClass x = classMap.get(gci3.getClassInSubClass());
    					OWLClass y = classMap.get(gci3.getSuperClass());
    					OWLObjectProperty prop = propMap.get(gci3.getPropertyInSubClass());
    					OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, x);
    					axiom = factory.getOWLSubClassOfAxiom(e, y);
    				}
    				else if (ax instanceof AxiomRI2)
    				{
    					AxiomRI2 ri2 = (AxiomRI2) ax;
    					OWLObjectProperty x = propMap.get(ri2.getSubProperty());
    					OWLObjectProperty y = propMap.get(ri2.getSuperProperty());
    					axiom = factory.getOWLSubObjectPropertyOfAxiom(x, y);
    				}
    				else if (ax instanceof AxiomRI3)
    				{
    					AxiomRI3 ri3 = (AxiomRI3) ax;
    					OWLObjectProperty x = propMap.get(ri3.getLeftSubProperty());
    					OWLObjectProperty y = propMap.get(ri3.getRightSubProperty());
    					OWLObjectProperty z = propMap.get(ri3.getSuperProperty());
    					List<OWLObjectProperty> chain = new ArrayList<OWLObjectProperty>();
    					chain.add(x);
    					chain.add(y);
    					axiom = factory.getOWLSubPropertyChainOfAxiom(chain, z);
    				}
    				else if (ax instanceof AxiomR)
    				{
    					AxiomR r = (AxiomR) ax;
    					OWLClass x = classMap.get(r.getSubClass());
    					OWLClass y = classMap.get(r.getClassInSuperClass());
    					OWLObjectProperty prop = propMap.get(r.getPropertyInSuperClass());
    					OWLClassExpression e = factory.getOWLObjectSomeValuesFrom(prop, y);
    					axiom = factory.getOWLSubClassOfAxiom(x, e);
    				}
    				else if (ax instanceof AxiomS)
    				{
    					AxiomS s = (AxiomS) ax;
    					OWLClass x = classMap.get(s.getSubClass());
    					OWLClass y = classMap.get(s.getSuperClass());
    					axiom = factory.getOWLSubClassOfAxiom(x, y);
    				}
    				if (!axiom.getClassesInSignature().contains(test))
    				{
    					axioms.add(axiom);
    				}
    			}
    			axiomsSets.add(axioms);
    		}
    		
        	explanations = new HashSet<OWLExplanation>();
        	for (Iterator<Set<OWLAxiom>> j = axiomsSets.iterator(); j.hasNext();)
        	{
        		OWLExplanation e;
				try {
					e = new OWLExplanation(j.next(), this);
					explanations.add(e);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
        	}
        	manager.removeAxiom(o, equiv);
        }
        
        return explanations;
        //============= END GETTING EXPLANATION ===============================
	}
	
/*	public Set<OWLLink> getDirectNeighbors (OWLConcept c)
	{
		Set<OWLLink> ownLinks = new HashSet<OWLLink>();
		Set<OWLClass> superClasses = reasoner.getSuperClasses(c.getOWLClass(), false).getFlattened();
		Stack<OWLClass> stck = new Stack<OWLClass>();
		stck.addAll(superClasses);
		superClasses.clear();
		double size = stck.size();
		for (int i = 0; i < size; i++)
		{
			OWLClass cl = stck.pop();
			Set<OWLClassExpression> clExps = cl.getSuperClasses(o);
			for (OWLClassExpression clExp: clExps)
			{
				if (clExp.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
				{
					OWLObjectSomeValuesFrom aux = (OWLObjectSomeValuesFrom) clExp;
					OWLClass destiny = aux.getFiller().asOWLClass();
					OWLConcept destinyConcept = getOWLConcept(destiny.toStringID());
					OWLObjectProperty p = aux.getProperty().asOWLObjectProperty();
					OWLRelation r = this.getOWLRelation(p.getIRI().toURI().toString());
					//====================BUILD AXIOM=================================
					OWLSubClassOfAxiom linkAxiom = buildAxiom(p, c.getOWLClass(), destiny);
					//============== END BUILDING AXIOM ================================
			        //============== GETTING EXPLANATION ===============================
			        Set<OWLExplanation> explanations = getExplanations(linkAxiom);
			        //============= END GETTING EXPLANATION ===============================
					ownLinks.add(new OWLLink(r, destinyConcept, explanations));
					//===================================
				}
			}
		}
		return ownLinks;
	}*/
	
	
	public Set<OWLRelation> getTransitiveOWLRelations()
	{
		Set<OWLRelation> transitives = new HashSet<OWLRelation>();
		
		for (Iterator<OWLRelation> i = relations.values().iterator(); i.hasNext();)
		{
			OWLRelation r = i.next();
			OWLObjectProperty oP = r.getOWLObjectProperty();
			if (oP.isTransitive(o))
				transitives.add(r);
				
		}
		return transitives;
	}
	
	public Set<List<OWLRelation>> getPropertyChains(OWLRelation r)
	{
		return getPropertyChains().get(r);
	}
	
	public Map<OWLRelation, Set<List<OWLRelation>>> getPropertyChains()
	{
		Map<OWLRelation, Set<List<OWLRelation>>> propertyChains = new HashMap<OWLRelation, Set<List<OWLRelation>>>();
		
		
		Set<OWLSubPropertyChainOfAxiom> axioms = o.getAxioms(AxiomType.SUB_PROPERTY_CHAIN_OF);
	
		for (Iterator<OWLSubPropertyChainOfAxiom> j = axioms.iterator(); j.hasNext();)
		{
			OWLSubPropertyChainOfAxiom oPChain = j.next();
			List<OWLObjectPropertyExpression> properties = oPChain.getPropertyChain();
			OWLObjectProperty op = oPChain.getSuperProperty().asOWLObjectProperty();
			OWLRelation r = this.getOWLRelation(op.toStringID());
			
			List<OWLRelation> relationChain = new ArrayList<OWLRelation>();
			for (Iterator<OWLObjectPropertyExpression> k = properties.iterator(); k.hasNext();)
			{
				OWLObjectProperty oChain = k.next().asOWLObjectProperty();
				relationChain.add(this.getOWLRelation(oChain.toStringID()));
			}
			Set<List<OWLRelation>> relationChains = propertyChains.get(r);
			if (relationChains == null)
			{
				relationChains = new HashSet<List<OWLRelation>>();
				propertyChains.put(r, relationChains);
			}
			relationChains.add(relationChain);
			
		}
		return propertyChains;
	}
	
	
	public Set<OWLLink> getIndividualOWLLink (MyOWLIndividual ind)
	{
		Set<OWLLink> ownLinks = new HashSet<OWLLink>();
		for (Iterator<OWLRelation> k = relations.values().iterator(); k.hasNext();)
		{
			OWLRelation r = k.next();
			Set<OWLNamedIndividual> set = reasoner.getObjectPropertyValues(ind.getOWLNamedIndividual(), r.getOWLObjectProperty()).getFlattened();
			for (Iterator<OWLNamedIndividual> i = set.iterator(); i.hasNext();)
			{
				OWLNamedIndividual neigh = i.next();
				MyOWLIndividual aux = individuals.get(neigh.toStringID());
				Set<OWLExplanation> exps = Collections.emptySet();//checkOWLLink(ind, r, aux);
				OWLLink link = new OWLLink(r, aux, exps);
				ownLinks.add(link);
			}
		}
		return ownLinks;
	}
	
	/*private void getOWLLinks(Set<OWLConcept> classes, Set<OWLRelation> objectProperties)
	{
		double progressCounter = 0.0;
		double totalLoops = classes.size()*classes.size()*objectProperties.size();
		//In this loop we check for each concept if it has any type of relation with any other in the ontology.
		for (Iterator<OWLConcept> i = classes.iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			Set<OWLLink> ownLinks = new HashSet<OWLLink>();
			for (Iterator<OWLConcept> j = classes.iterator(); j.hasNext();)
			{
				OWLConcept d = j.next();
				for (Iterator<OWLRelation> k = objectProperties.iterator(); k.hasNext();)
				{
					OWLRelation r = k.next();
					Set<OWLExplanation> exps = checkOWLLink(c, r, d); 
					if (exps != null)
					{
						OWLLink link = new OWLLink(r, d, exps); //All the links, inferred and not inferred, have explanations
						ownLinks.add(link);
					}
					progressCounter++;
				}
				
			}
            //Set neighbors of OWLConcepts
			c.setNeighbors(ownLinks);
			System.out.println(progressCounter*100/totalLoops + "%");
		}
	}*/
	
	public boolean isPropertyinSomePropertyChain(OWLRelation p)
	{
		for (Iterator<OWLRelation> i = propertyChains.keySet().iterator(); i.hasNext();)
		{
			OWLRelation r = i.next();
			Set<List<OWLRelation>> set = propertyChains.get(r);
			for (Iterator<List<OWLRelation>> j = set.iterator(); j.hasNext();)
			{
				List<OWLRelation> list = j.next();
				if (list.contains(p))
					return true;
			}
		}
		return false;
	}
	
	
	public Set<OWLConcept> getIsland(OWLConcept c)
	{
		return getIsland(c, new HashSet<OWLConcept>());
	}
	
	private Set<OWLConcept> getIsland(OWLConcept c, Set<OWLConcept> visited)
	{
		
		Set<OWLConcept> island = new HashSet<OWLConcept>();
		
		Set<OWLClassExpression> superClasses = c.getOWLClass().getSuperClasses(o);
		Stack<OWLClassExpression> stck = new Stack<OWLClassExpression>();
		stck.addAll(superClasses);
		superClasses.clear();
		double size = stck.size();
		for (int i = 0; i < size; i++)
		{
			OWLClassExpression clExp = stck.pop();
			if (clExp.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
			{
				OWLObjectSomeValuesFrom aux = (OWLObjectSomeValuesFrom) clExp;
				OWLClass destiny = aux.getFiller().asOWLClass();
				OWLConcept destinyConcept = getOWLConcept(destiny.toStringID());
				OWLObjectProperty p = aux.getProperty().asOWLObjectProperty();
				if (!visited.contains(destinyConcept))
				{
					island.add(destinyConcept);
					visited.add(destinyConcept);
					//if (p.isTransitive(o) || isPropertyinSomePropertyChain(this.getOWLRelation(p.toStringID())))
						island.addAll(getIsland(destinyConcept, visited));
				}
			}
			/*if (clExp.getClassExpressionType() == ClassExpressionType.OWL_CLASS)
			{
				OWLConcept parentConcept = getOWLConcept(((OWLClass) clExp).toStringID()); 
				if (!visited.contains(parentConcept))
				{
					island.addAll(getIsland(parentConcept, visited));
				}
			}*/
		}
		return island;
	}
	
	private Set<OWLExplanation> checkOWLLink(OWLConcept c1, OWLRelation r, OWLConcept c2)
	{
		OWLClass a = c1.getOWLClass();
		OWLClass b = c2.getOWLClass();
		OWLObjectProperty p = r.getOWLObjectProperty();
        OWLObjectSomeValuesFrom relationAxiom = factory.getOWLObjectSomeValuesFrom(p, b);
        OWLSubClassOfAxiom linkAxiom = factory.getOWLSubClassOfAxiom(a, relationAxiom);
        
        //Maybe we have to consider not only the "some values from", but also "all values from"
        Set<OWLExplanation> explanations = null;
        if (o.containsAxiom(linkAxiom))
        {
        	explanations = Collections.emptySet();
        	return explanations;
        }
        
        /*OWLClassExpression negation = factory.getOWLObjectComplementOf(relationAxiom);
        Set<OWLClassExpression> subsumption = new HashSet<OWLClassExpression>();
        subsumption.add(a);
        subsumption.add(negation);
        OWLObjectIntersectionOf subsumptionAxiom = factory.getOWLObjectIntersectionOf(subsumption);*/
        
        if (reasoner.isEntailed(linkAxiom)) //If the axiom is explicit in the ontology does not have explanation
        //if (reasoner.getSubClasses(relationAxiom, false).containsEntity(a))
        //if (!reasoner.isSatisfiable(subsumptionAxiom))
        {
        	/*startTime = System.nanoTime();
        	explanations = getExplanations(linkAxiom);//new HashSet<OWLExplanation>();
        	estimatedTime = (System.nanoTime() - startTime)/1000000;
        	System.out.println("Classic Explanation: " + estimatedTime + " " + explanations);*/
        	/*Set<Explanation<OWLAxiom>> expAxioms = expl.getExplanations(linkAxiom, 1);
        	for (Iterator<Explanation<OWLAxiom>> i = expAxioms.iterator(); i.hasNext();)
        	{
        		OWLExplanation e;
				try {
					e = new OWLExplanation(i.next().getAxioms(), this);
					explanations.add(e);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
        	}*/
        	//startTime = System.nanoTime();
        	explanations = getExplanations(linkAxiom);
        	if (explanations.size() > 1)
        	{
        		OWLExplanation exp = explanations.iterator().next();
        		explanations.clear();
        		explanations.add(exp);
        	}
        	//estimatedTime = (System.nanoTime() - startTime)/1000000;
        	//System.out.println("New Explanation: " + estimatedTime + " " + explanations);
        }
        return explanations;
	}
	
	private Set<OWLExplanation> checkOWLLink(MyOWLIndividual c1, OWLRelation r, MyOWLIndividual c2)
	{
		OWLNamedIndividual a = c1.getOWLNamedIndividual();
		OWLNamedIndividual b = c2.getOWLNamedIndividual();
		OWLObjectProperty p = r.getOWLObjectProperty();
        OWLObjectPropertyAssertionAxiom linkAxiom = factory.getOWLObjectPropertyAssertionAxiom(p, a, b);
        
        //Maybe we have to consider not only the "some values from", but also "all values from"
        Set<OWLExplanation> explanations = null;
        if (o.containsAxiom(linkAxiom))
        {
        	explanations = Collections.emptySet();
        	return explanations;
        }
        if (reasoner.isEntailed(linkAxiom)) //If the axiom is explicit in the ontology does not have explanation
        {
        	explanations = new HashSet<OWLExplanation>();
        	Set<Explanation<OWLAxiom>> expAxioms = expl.getExplanations(linkAxiom, 1);
        	for (Iterator<Explanation<OWLAxiom>> i = expAxioms.iterator(); i.hasNext();)
        	{
        		OWLExplanation e;
				try {
					e = new OWLExplanation(i.next().getAxioms(), this);
					explanations.add(e);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
        	}
        }
        return explanations;
	}
	
	/*private void startReasoner(){
		OWLReasonerFactory reasonerFactory = new Reasoner.ReasonerFactory(); //new JcelReasonerFactory(); //ElkReasonerFactory(); new JFactFactory(); //new PelletReasonerFactory(); 
		Configuration configuration = new Configuration();
		configuration.ignoreUnsupportedDatatypes = true;
		configuration.throwInconsistentOntologyException = false; //Just for HermiT
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.WARN);
		reasoner =  reasonerFactory.createReasoner(o, configuration);
        reasoner.precomputeInferences(InferenceType.CLASS_ASSERTIONS);
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        reasoner.precomputeInferences(InferenceType.OBJECT_PROPERTY_HIERARCHY);
        reasoner.precomputeInferences(InferenceType.OBJECT_PROPERTY_ASSERTIONS);
        reasoner.precomputeInferences(InferenceType.DISJOINT_CLASSES);
        ExplanationGeneratorFactory<OWLAxiom> genFac = ExplanationManager.createExplanationGeneratorFactory(reasonerFactory); //new ElkReasonerFactory());
        expl = genFac.createExplanationGenerator(o);
        reasonerExpl = new ELKOWLOntologyReasoner(o);
        reasonerExpl.doInference();
        repository = new MyAxiomRepository(reasonerExpl.getClassGraph(),	reasonerExpl.getRelationSet(),	reasonerExpl.getNormalizedIntegerAxiomSet()						);
		repository.createIndex();
	}*/
	
	private void startReasoner(){
		OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();//Reasoner.ReasonerFactory(); //new JcelReasonerFactory(); // new JFactFactory(); //new PelletReasonerFactory(); // 
		OWLReasonerConfiguration configuration = new ElkReasonerConfiguration();
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.WARN);
		reasoner =  reasonerFactory.createReasoner(o, configuration);
        reasoner.precomputeInferences(InferenceType.CLASS_ASSERTIONS);
        reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        reasoner.precomputeInferences(InferenceType.OBJECT_PROPERTY_HIERARCHY);
        reasoner.precomputeInferences(InferenceType.OBJECT_PROPERTY_ASSERTIONS);
        reasoner.precomputeInferences(InferenceType.DISJOINT_CLASSES);
        ExplanationGeneratorFactory<OWLAxiom> genFac = ExplanationManager.createExplanationGeneratorFactory(reasonerFactory); //new ElkReasonerFactory());
        expl = genFac.createExplanationGenerator(o);
        reasonerExpl = new ELKOWLOntologyReasoner((ElkReasoner) reasoner, o);
        reasonerExpl.doInference();
        repository = new MyAxiomRepository(reasonerExpl.getClassGraph(),	reasonerExpl.getRelationSet(),	reasonerExpl.getNormalizedIntegerAxiomSet()						);
		repository.createIndex();
	}
	
	public void disposeReasoner()
	{
		reasoner.dispose();
	}

	public Set<OWLConcept> getConcepts() {
		return new HashSet<OWLConcept>(concepts.values());
	}
	
	public void removeConcept(OWLConcept c)
	{
		c.dispose();
		//this.concepts.remove(c);
	}
	
	public OWLConcept getOWLConcept (String uri)
	{
		OWLConcept con = concepts.get(uri);
		/*if (con == null)
		{
			con = new OWLConcept(factory.getOWLClass(IRI.create(uri)), this);
			concepts.put(uri, con);
		}*/
		return con;
	}
	
	public MyOWLIndividual getMyOWLIndividual (String uri)
	{
		MyOWLIndividual con = individuals.get(uri);
		if (con == null)
		{
			con = new MyOWLIndividual(factory.getOWLNamedIndividual(IRI.create(uri)), this);
			individuals.put(uri, con);
		}
		return con;
	}
	
	public Set<OWLConcept> getSubConcepts(OWLConcept c)
	{
		Set<OWLClass> classes = reasoner.getSubClasses(c.getOWLClass(), false).getFlattened();
		Set<OWLConcept> subConcepts = new HashSet<OWLConcept>();
		for (Iterator<OWLClass> i = classes.iterator(); i.hasNext();)
		{
			OWLClass cl = i.next();
			subConcepts.add(this.getOWLConcept(cl.toStringID()));
		}
		return subConcepts;
	}
	
	public Set<OWLRelation> getSubRelations(OWLRelation c)
	{
		Set<OWLObjectPropertyExpression> relations = reasoner.getSubObjectProperties(c.getOWLObjectProperty(), false).getFlattened();
		Set<OWLRelation> subRelations = new HashSet<OWLRelation>();
		for (Iterator<OWLObjectPropertyExpression> i = relations.iterator(); i.hasNext();)
		{
			OWLObjectProperty cl = i.next().asOWLObjectProperty();
			subRelations.add(this.getOWLRelation(cl.toStringID()));
		}
		return subRelations;
	}
	
	
	public OWLNamedIndividual getOWLIndividual (String uri)
	{
		return factory.getOWLNamedIndividual(IRI.create(uri));
	}
	
	public boolean isSatisfiable(OWLClass cl)
	{
		return reasoner.isSatisfiable(cl);
	}
	
	public boolean isSubClassOf(OWLClass sub, OWLClass sup)
	{
		Set<OWLClass> anc = getSuperClasses(sub);
		return anc.contains(sup);
	}
	
	private Set<OWLClass> getSuperClasses(OWLClass sub)
	{
		Set<OWLClass> anc = ancestors.get(sub);
		if (anc == null)
		{
			anc = reasoner.getSuperClasses(sub, false).getFlattened();
			ancestors.put(sub, anc);
		}
		return anc;
	}
	
	public Set<OWLConcept> getAncestors(OWLConcept c)
	{
		Set<OWLClass> classes = getSuperClasses(c.getOWLClass());
		Set<OWLConcept> concepts = new HashSet<OWLConcept>();
		for (OWLClass cl: classes)
		{
			concepts.add(this.getOWLConcept(cl.toStringID()));
		}
		return concepts;
	}
	
	public boolean isOfType(OWLNamedIndividual ind, OWLClass c)
	{
		return reasoner.getTypes(ind, false).containsEntity(c);
	}

	public Set<OWLRelation> getRelations() {
		return new HashSet<OWLRelation>(relations.values());
	}
	
	public OWLRelation getOWLRelation (String uri)
	{
		return relations.get(uri);
	}

	public OWLObjectProperty getOWLObjectProperty(String uri)
	{
		return factory.getOWLObjectProperty(IRI.create(uri));
	}
	
	private <T,S> T profLCS (Set<T> setX, Set<T> setY, T x, T y)
	{
		if (x == y)
			return x;

		Set<T> common = new HashSet<T>(setX);
		common.retainAll(setY);
		
		T lcs = common.iterator().next();

		int maxProf = prof(lcs);
		for (Iterator<T> i = common.iterator(); i.hasNext(); )
		{
			T aux = (T) i.next();
			
			if (prof(aux) > maxProf )
			{
				maxProf = prof(aux);
				lcs = aux;
			}
		}
		return lcs;
	}
	
	public Set<OWLObjectPropertyExpression> getSuperObjectProperties(OWLObjectProperty x, boolean direct)
	{
		Set<OWLObjectPropertyExpression> superProp = new HashSet<OWLObjectPropertyExpression>();
		superProp.add(factory.getOWLTopObjectProperty());
		if (direct)
		{
			superProp.addAll(x.getSuperProperties(o));
			return superProp;
		}
		
		Set<OWLObjectPropertyExpression> step = x.getSuperProperties(o);
		List<OWLObjectPropertyExpression> list = new ArrayList<OWLObjectPropertyExpression>(step);
		while (list.size() > 0)
		{
			step = list.get(0).getSuperProperties(o);
			superProp.add(list.get(0));
			list.remove(0);
			list.addAll(step);
		}
		return superProp;
	}
	
	
	public double taxonomicPropertySimilarity (OWLObjectProperty x, OWLObjectProperty y)
	{	
		Set<OWLObjectPropertyExpression> setX = this.getSuperObjectProperties(x, false); 
		setX.add(x);
		Set<OWLObjectPropertyExpression> setY = this.getSuperObjectProperties(y, false);
		setY.add(y);
		
		OWLObjectProperty lcs = (OWLObjectProperty) profLCS(setX, setY, x, y);
		double profLCS = prof(lcs);
		
		double dxa = dist(x, lcs);
		double dxroot = profLCS + dxa;
		double dya = dist(y, lcs);
		double dyroot = profLCS + dya;
		double dtax = (dxa + dya)/(dxroot + dyroot);
		
		return 1-dtax;
	}
	
	public OWLConcept getLCS(OWLConcept a, OWLConcept b)
	{
		OWLConceptComparison comparison = new OWLConceptComparison(a, b);
		OWLConcept lcsConcept = lcas.get(comparison);//null;//
		if (lcsConcept == null)
		{
			OWLClass x = a.getOWLClass(), y = b.getOWLClass();
			Set<OWLClass> setX = getSuperClasses(x);//reasoner.getSuperClasses(x, false).getFlattened(); //this.getSuperClasses(x, false);
			setX.add(x);
			Set<OWLClass> setY = getSuperClasses(y);//reasoner.getSuperClasses(y, false).getFlattened(); //this.getSuperClasses(y, false);
			setY.add(y);
			OWLClass lcs = profLCS(setX, setY, x, y);
			lcsConcept = this.getOWLConcept(lcs.toStringID());
			if (storing)
				lcas.put(comparison, lcsConcept);
		}
		
		return lcsConcept;
	}
	
/*	public Set<OWLConcept> getDCA(OWLConcept a, OWLConcept b)
	{
		OWLConceptComparison comparison = new OWLConceptComparison(a, b);
		Set<OWLConcept> dcas = disAncestors.get(comparison);
		
		if (dcas == null)
		{
			Set<OWLClass> aA = this.getSuperClasses(a.getOWLClass());
			Set<OWLClass> aB = this.getSuperClasses(b.getOWLClass());
			Set<OWLClass> common = new HashSet<OWLClass>(aA);
			common.retainAll(aB);
			Map<OWLClass, Integer> mapA = new HashMap<OWLClass, Integer>();
			Map<OWLClass, Integer> mapB = new HashMap<OWLClass, Integer>();
			getPath(a.getOWLClass(), mapA);
			mapA.put(a.getOWLClass(), 1);
			getPath(b.getOWLClass(), mapB);
			mapB.put(b.getOWLClass(), 1);
			Map<Integer, Set<OWLClass>> pathsClasses = new HashMap<Integer, Set<OWLClass>>();
			for (OWLClass cl: common)
			{
				Integer iA = mapA.get(cl);
				Integer iB = mapB.get(cl);
				
				Set<OWLClass> aux = pathsClasses.get(Math.abs(iA - iB));
				if (aux == null)
				{
					aux = new HashSet<OWLClass>();
					pathsClasses.put(Math.abs(iA - iB), aux);
				}
				aux.add(cl);
			}
			dcas = new HashSet<OWLConcept>();
			
			for (Integer dist: pathsClasses.keySet())
			{
				Set<OWLClass> aux = pathsClasses.get(dist);
				double max = 0;
				OWLConcept maxCL = null;
				for (OWLClass cl: aux)
				{
					OWLConcept con = concepts.get(cl.toStringID());
					if (con.getIC() >= max)
					{
						max = con.getIC();
						maxCL = con;
					}
				}
				dcas.add(maxCL);
			}
			disAncestors.put(comparison, dcas);
		}
		return dcas;
	}*/
	
	private void getPath(OWLClass a, Map<OWLClass, Integer> map)
	{
		
		Set<OWLClassExpression> aA = a.getSuperClasses(o);
		for (OWLClassExpression exp: aA)
		{
			if (!exp.isAnonymous())
			{
				OWLClass clA = exp.asOWLClass();
				Integer numPath = map.get(clA);
				if (numPath == null)
					numPath = 0;
				map.put(clA, numPath + 1);
				getPath(clA, map);
			}
		}
	}
	
	public OWLConcept getLCS(MyOWLIndividual a, MyOWLIndividual b)
	{
		OWLNamedIndividual x = a.getOWLNamedIndividual(), y = b.getOWLNamedIndividual();
		Set<OWLClass> setX = reasoner.getTypes(x, false).getFlattened();
		Set<OWLClass> setY = reasoner.getTypes(y, false).getFlattened();
		OWLClass lcs = profLCS(setX, setY, setX.iterator().next(), null);
		return this.getOWLConcept(lcs.toStringID());
	}
	
	public double taxonomicClassSimilarity (OWLConcept x, OWLConcept y)
	{
		OWLConcept lcs = getLCS(x, y);
		
		//if (roots.contains(lcs))
		//	return 0;
		
		double profLCS = prof(lcs.getOWLClass());
		
		double dxa = dist(x.getOWLClass(), lcs.getOWLClass());
		double dxroot = profLCS + dxa;
		double dya = dist(y.getOWLClass(), lcs.getOWLClass());
		double dyroot = profLCS + dya;
		double num = dxa + dya;
		double den = dxroot + dyroot;
		double dtax = num/den;
		dtax = 1.0 - dtax;
		
		return dtax;
	}
	
	
	private Set<OWLClass> getTypes(OWLNamedIndividual ind, boolean direct)
	{
		Set<OWLClass> classes = new HashSet<OWLClass>();
		Set<OWLClassExpression> classExprs = ind.getTypes(o);
		
		if (direct)
		{
			for (OWLClassExpression clExp: classExprs)
			{
				classes.add(clExp.asOWLClass());
			}
		}
		else
		{
			for (OWLClassExpression clExp: classExprs)
			{
				classes.addAll(getSuperClasses(clExp.asOWLClass()));//reasoner.getSuperClasses(clExp, false).getFlattened());
			}
			for (OWLClassExpression clExp: classExprs)
			{
				classes.add(clExp.asOWLClass());
			}
		}
		return classes;
	}
	
	public double taxonomicIndividualSimilarity (OWLLogicalEntity x, OWLLogicalEntity y)
	{
		Set<OWLClass> setX;
		Set<OWLClass> setY;
		OWLClass lcs = null;
		if (x.isOWLNamedIndividual() && y.isOWLNamedIndividual())
		{
			setX = /*reasoner.*/getTypes(x.asOWLNamedIndividual(), false);//.getFlattened();
			setY = /*reasoner.*/getTypes(y.asOWLNamedIndividual(), false);//.getFlattened();
			lcs = profLCS(setX, setY, setX.iterator().next(), null);
		}
		
		if (x.isOWLClass() && y.isOWLClass())
		{
			OWLClass xC = x.asOWLClass();
			OWLClass yC = y.asOWLClass();
			setX = getSuperClasses(xC);//reasoner.getSuperClasses(xC, false).getFlattened();
			setX.add(xC);
			setY = getSuperClasses(yC);//reasoner.getSuperClasses(yC, false).getFlattened();
			setY.add(yC);
			lcs = profLCS(setX, setY, xC, yC);
		}
		
		
		
		//=======================Only for ComparisonCosine
		//OWLClass obsolete = factory.getOWLClass(IRI.create("http://www.geneontology.org/formats/oboInOwl#ObsoleteClass"));
		/*OWLAnnotationProperty deprecated = factory.getOWLAnnotationProperty(IRI.create("http://www.w3.org/2002/07/owl#deprecated"));
		Set<OWLAnnotation> annX = x.getAnnotations(o, deprecated);
		if (annX.iterator().next().isDeprecatedIRIAnnotation())
			System.out.println("Deprecated");*/
		//if (setX.contains(obsolete) || setY.contains(obsolete))
		//	return 0;
		//=======================END
		
		if (lcs == null)
			return 0;
		
		double profLCS = prof(lcs);
		
		double dxa = dist(x, lcs);
		double dxroot = profLCS + dxa;//dist(x, root);
		double dya = dist(y, lcs);
		double dyroot = profLCS + dya;//dist(y, root);
		double num = dxa + dya;
		double den = dxroot + dyroot;
		double dtax = num/den;
		dtax = 1.0 - dtax;
		
		/*System.out.println(lcs +  " " + profLCS);
		System.out.println(dxa + " " + dya);
		System.out.println(x + " " + y + " " + dtax);*/
		return dtax;
	}
	
	
	
	
	
	private void setDistance(OWLClass c1, OWLClass c2, int d)
	{
		Map<OWLClass, Integer> aux = conceptDistances.get(c1);
		
		if (aux == null)
		{
			aux = new HashMap<OWLClass, Integer>();
			if (storing)
				conceptDistances.put(c1, aux);
		}
		aux.put(c2, d);
	}
	
	private int getDistance(OWLClass c1, OWLClass c2)
	{
		Map<OWLClass, Integer> aux = conceptDistances.get(c1);
		
		if (aux == null)
			return -1;
		else
		{
			Integer d = aux.get(c2);
			if (d == null)
				return -1;
			else
				return d;
		}
	}
	
	
	public <T> int dist(T c1, T c2)
	{
		int depth = 0;
		if (c1 instanceof OWLClass)
		{
			int dist = getDistance((OWLClass)c1, (OWLClass)c2);
			if (dist != -1)
				return dist;
			Set<OWLClassExpression> c = new HashSet<OWLClassExpression>();
			c.add((OWLClass) c1);
			while (!c.contains(c2) && !c.isEmpty())
			{
				Set<OWLClassExpression> superClasses = new HashSet<OWLClassExpression>();
				for (Iterator<OWLClassExpression> i = c.iterator(); i.hasNext();)
				{
					OWLClassExpression aux = i.next();
					if (!aux.isAnonymous())
					{
						OWLClass cl = aux.asOWLClass();
						superClasses.addAll(cl.getSuperClasses(o));
					}
				}
				c = superClasses;
				depth++;				
			}
			setDistance((OWLClass)c1, (OWLClass)c2, depth);
		}
		else if (c1 instanceof OWLObjectProperty)
		{
			Set<OWLObjectPropertyExpression> c = new HashSet<OWLObjectPropertyExpression>();
			c.add((OWLObjectPropertyExpression) c1);
			while (!c.contains(c2) && !c.isEmpty())
			{
				Set<OWLObjectPropertyExpression> superObjectProperties = new HashSet<OWLObjectPropertyExpression>();
				for (Iterator<OWLObjectPropertyExpression> i = c.iterator(); i.hasNext();)
				{
					OWLObjectPropertyExpression aux = i.next();
					if (!aux.isAnonymous())
						superObjectProperties.addAll(aux.getSuperProperties(o));
				}
				c = superObjectProperties;
				depth++;				
			}
		} else if (c1 instanceof OWLNamedIndividual)
		{
			 Set<OWLClassExpression> c = new HashSet<OWLClassExpression>();
			 Set<OWLClass> auxSet = reasoner.getTypes((OWLNamedIndividual) c1, true).getFlattened();
			 for (OWLClass cl: auxSet)
			 {
				 c.add(cl);
			 }
			 while (!c.contains(c2) && !c.isEmpty())
			 {
				Set<OWLClassExpression> superClasses = new HashSet<OWLClassExpression>();
				for (Iterator<OWLClassExpression> i = c.iterator(); i.hasNext();)
				{
					OWLClassExpression aux = i.next();
					if (!aux.isAnonymous())
					{
						OWLClass cl = aux.asOWLClass();
						superClasses.addAll(cl.getSuperClasses(o));
					}
				}
				c = superClasses;
				depth++;
			 }
		}
		else	try {
				throw new Exception("dist() does not accept objects of type " + c1.getClass());
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		return depth;
	}
	
	public <T> int prof(T _class)
	{
		int depth = 0;
		if (_class instanceof OWLClass)
		{
			if (conceptProfs.get(_class) != null)
				return conceptProfs.get(_class);
			
			depth = dist (_class, factory.getOWLThing());// - 1;
			if (storing)
				conceptProfs.put((OWLClass) _class, depth);
		}
		else if (_class instanceof OWLObjectProperty)
		{
			if (relationProfs.get(_class) != null)
				return relationProfs.get(_class);
			depth = dist (_class, factory.getOWLTopObjectProperty());
			relationProfs.put((OWLObjectProperty) _class, depth);
		} else
			try {
				throw new Exception("prof() does not accept objects of type " + _class.getClass());
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		return depth;
	}
	
	
	public String getLabel(OWLConcept c)
	{
		OWLClass x = c.getOWLClass();
		OWLAnnotationProperty label = factory.getOWLAnnotationProperty(IRI.create("http://www.w3.org/2000/01/rdf-schema#label"));
		Set<OWLAnnotation> annX = x.getAnnotations(o, label);
		OWLAnnotation a = annX.iterator().next(); 
		OWLLiteral lit = (OWLLiteral) a.getValue();
		String v = lit.getLiteral();
		return v;
	}
	
	
	
	public static void main(String[] args)
	{
		/*String ontFile1 = "/home/traverso/Schreibtisch/test.rdf";
		MyOWLOntology oDBP = new MyOWLOntology(ontFile1, "http://dbpedia.org/ontology/");
		
		MyOWLIndividual ia = oDBP.getMyOWLIndividual("http://dbpedia.org/resource/Parable_of_the_Sower_(novel)");
		MyOWLIndividual ib = oDBP.getMyOWLIndividual("http://dbpedia.org/resource/Parable_of_the_Talents_(novel)");
		System.out.println(ia.similarity(ib));*/

		/*Iterator<OWLRelation> j = o.getRelations().iterator();
		OWLRelation x = j.next();
		OWLRelation y = j.next();
		o.similarity(x, y);
		System.out.println(x + " " + y + " " + o.similarity(x,y));*/
		
		Map<String, String> ontPrefix = new HashMap<String,String>();
		ontPrefix.put("src/main/resources/dataset3/", "http://purl.org/obo/owl/GO#");
		ontPrefix.put("src/main/resources/dataset32014/", "http://purl.obolibrary.org/obo/");
		String prefix = "src/main/resources/dataset3/";
		String ontFile = prefix + "goProtein/goEL.owl";
		MyOWLOntology o = new MyOWLOntology(ontFile, ontPrefix.get(prefix));//"http://purl.obolibrary.org/obo/");
		
		String comparisonFile = prefix + "proteinpairs.txt";
		List<ComparisonResult> comparisons = DatasetTest.readComparisonFile(comparisonFile);
		String[] files = {prefix + "bpNew"};
		//InformationContent ic = new InformationContent(comparisons, files, o);
		//InformationContent ic = new InformationContent("src/main/resources/dataset3/corpusCESSM2008.txt", o);
		
		/*MyOWLIndividual ia = o.getMyOWLIndividual(ontPrefix.get(prefix) + "GO_0055114");
		MyOWLIndividual ib = o.getMyOWLIndividual(ontPrefix.get(prefix) + "GO_0030259");
		System.out.println(ib.similarity(ia));
		
		List<ComparisonResult> comparisons = DatasetTest.readComparisonFile(prefix + "termPairs.txt");
		Set<OWLConcept> anns = new HashSet<OWLConcept>();
		for (ComparisonResult c: comparisons)
		{
			OWLConcept a = o.getOWLConcept(ontPrefix.get(prefix) + c.getConceptA().replace(":", "_"));
			OWLConcept b = o.getOWLConcept(ontPrefix.get(prefix) + c.getConceptB().replace(":", "_"));
			if (a == null || b == null)
				System.out.println("cuidado");
			anns.add(a);
			anns.add(b);
			
		}
		o.setOWLLinks(anns);
		for (ComparisonResult c: comparisons)
		{
			OWLConcept a = o.getOWLConcept(ontPrefix.get(prefix) + c.getConceptA().replace(":", "_"));
			OWLConcept b = o.getOWLConcept(ontPrefix.get(prefix) + c.getConceptB().replace(":", "_"));
			System.out.println(a.getName() + " " + b.getName() + " " + a.similarity(b));
		}*/
		
		
		
		OWLConcept a = o.getOWLConcept(ontPrefix.get(prefix) + "GO_0006355");
		OWLConcept b = o.getOWLConcept(ontPrefix.get(prefix) + "GO_0006342");
		Set<OWLConcept> anns = new HashSet<OWLConcept>();
		anns.add(a);
		anns.add(b);
		o.setOWLLinks(anns);
		Set<OWLLink> neighA = a.getNeighbors();
		Set<OWLLink> neighB = b.getNeighbors();
		System.out.println(b.similarity(a));//.taxonomicSimilarity(a));
		
		OWLRelation r1 = o.getOWLRelation("http://purl.obolibrary.org/obo/RO_0002213");//"("http://purl.org/obo/owl/obo#positively_regulates");
		System.out.println(o.getPropertyChains(r1));
		OWLRelation r2 = o.getOWLRelation("http://purl.obolibrary.org/obo/RO_0002211"); //("http://purl.org/obo/owl/obo#regulates");
		System.out.println(o.getPropertyChains(r2));
		System.out.println(r1.similarity(r2));
	
		
	}
}
