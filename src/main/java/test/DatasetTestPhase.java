package test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import ontologyManagement.MyOWLOntology;
import ontologyManagement.OWLConcept;
import similarity.matching.AnnSim;
import similarity.matching.OnJaccard;

public class DatasetTestPhase {

	public static Set<OWLConcept> getFilteredConceptAnnotations(String conceptName, String folder, MyOWLOntology o)
	{
		Set<OWLConcept> concepts = DatasetTest.getConceptAnnotations(conceptName, folder, o, true);
		Set<OWLConcept> auxSet = new HashSet<OWLConcept>(concepts);
		for (OWLConcept c: auxSet)
		{
			for (OWLConcept d: auxSet)
			{
				if (!c.equals(d))
				{
					if (d.isSubConceptOf(c))
						concepts.remove(c);
				}
			}
		}
		return concepts;
	}
	
	public static void main(String[] args) throws Exception {
		Map<String, String> ontPrefix = new HashMap<String,String>();
		ontPrefix.put("src/main/resources/dataset3/", "http://purl.org/obo/owl/GO#");
		ontPrefix.put("src/main/resources/dataset32014/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2008/", "http://purl.org/obo/owl/GO#");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2010/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2012/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2014/", "http://purl.obolibrary.org/obo/");
		String[] p = {"src/main/resources/dataset32014/"};
		for (String prefix: p)
		{
			String ontFile = prefix + "goProtein/goEL.owl";
			MyOWLOntology o = new MyOWLOntology(ontFile, ontPrefix.get(prefix));
			String comparisonFile = prefix + "proteinpairs.txt";
			List<ComparisonResult> comparisons = DatasetTest.readComparisonFile(comparisonFile);
			String branch = "bp";
			String[] files = {prefix + "mf"};//, prefix + "mf", prefix + "cc"};
			
			Set<String> entities = new HashSet<String>();
			File f = new File(files[0]);
			File[] pNames = f.listFiles();
			for (File x: pNames)
			{
				entities.add(x.getName());
			}
			
			//InformationContent ic = new InformationContent(entities, files[0], o);
			//InformationContent ic = new InformationContent(entities, prefix + "corpusCESSM.txt", files[0], o);//(comparisons, files, o);
			
			
			//================= GETTING OWLCONCEPT NEIGHBORHOODS ==============
			double startRelTime = System.nanoTime();
			Set<OWLConcept> anns = DatasetTest.getOntologyTerms(comparisons, files, o);
			o.setOWLLinks(anns);
			double estimatedRelTime = (System.nanoTime() - startRelTime)/1000000;
			System.out.println(estimatedRelTime/1000/60);
			//================ END GETTING NEIGHBORHOOODS ====================
			//=================== GETTING INFORMATION CONTENT ======================
			
 			
			//=================== END GETTING INFORMATION CONTENT ======================
			//================ FINDING WHICH COMPARISONS HAVE TO BE PERFORMED ==========
			Set<OWLConceptComparison> conceptComparisons = new HashSet<OWLConceptComparison>();
			for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
			{
				ComparisonResult comp = i.next();
				for (String file:files)
				{
					//Set<OWLConcept> a = /*DatasetTest.getConceptAnnotations*/getFilteredConceptAnnotations(comp.getConceptA(), file, o);
					//Set<OWLConcept> b = /*DatasetTest.getConceptAnnotations*/getFilteredConceptAnnotations(comp.getConceptB(), file, o);
					Set<OWLConcept> a = DatasetTest.getConceptAnnotations(comp.getConceptA(), file, o, false);
					Set<OWLConcept> b = DatasetTest.getConceptAnnotations(comp.getConceptB(), file, o, false);
					for (OWLConcept c1: a)
					{
						for (OWLConcept c2: b)
						{
							conceptComparisons.add(new OWLConceptComparison(c1, c2));
						}
					}
				}
			}
			System.out.println("Concept Comparisons: " + conceptComparisons.size());
			//================ END FINDING COMPARISONS ================================
			//================ COMPUTING COMPARISONS ==================================
			startRelTime = System.nanoTime();
			Map<OWLConceptComparison, Double> costMatrix = new HashMap<OWLConceptComparison, Double>();
			for (OWLConceptComparison comparison: conceptComparisons)
			{
				Double sim = comparison.getConceptA().similarity(comparison.getConceptB());
 				costMatrix.put(comparison, sim);
			}
			estimatedRelTime = (System.nanoTime() - startRelTime)/1000000;
			System.out.println(estimatedRelTime/1000/60);
			//================ END COMPUTING COMPARISONS ===========================
			PrintWriter generalWriter = new PrintWriter(prefix + "results.txt", "UTF-8");
			Map<String, PrintWriter> writers = new HashMap<String, PrintWriter>();
			for (String file:files)
			{
				writers.put(file, new PrintWriter(prefix + file.replaceAll(prefix, "") + "results.txt"));
			}
			//generalWriter.println("Protein1\tProtein2\tSimilarity");
			int counter = 0, total = comparisons.size();
			//================ COMPUTING MATCHING ===============================
			startRelTime = System.nanoTime();
			AnnSim bpm = new AnnSim(costMatrix);
			for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
			{
				ComparisonResult comp = i.next();
				double sim = 0;
				double totalEstimatedTime = 0;
				for (String file:files)
				{
					//Set<OWLConcept> a = getFilteredConceptAnnotations(comp.getConceptA(), file, o);
					//Set<OWLConcept> b = getFilteredConceptAnnotations(comp.getConceptB(), file, o);
					Set<OWLConcept> a = DatasetTest.getConceptAnnotations(comp.getConceptA(), file, o, false);
					Set<OWLConcept> b = DatasetTest.getConceptAnnotations(comp.getConceptB(), file, o, false);
					Set<OWLConcept> intersection = new HashSet<OWLConcept>(a);
					intersection.retainAll(b);
					Set<OWLConcept> union = new HashSet<OWLConcept>(a);
					union.addAll(b);
					double startTime = System.nanoTime();  
					double aux = bpm.matching(a, b, null, null);
					double estimatedTime = System.nanoTime() - startTime;
					totalEstimatedTime += estimatedTime/1000000;
					sim = aux;
					comp.setSimilarity(sim);
					writers.get(file).println(comp);
					System.out.println(comp + "\t" + totalEstimatedTime + "\t" + counter++ + "/" + total + "\t" + a.size() + "\t" + b.size());
					generalWriter.println(comp + "\t" + totalEstimatedTime + "\t" + a.size() + "\t" + b.size());
				}
			}
			generalWriter.close();
			for (String file:files)
			{
				writers.get(file).close();
			}
			estimatedRelTime = (System.nanoTime() - startRelTime)/1000000;
			System.out.println(estimatedRelTime/1000/60);;
			o.disposeReasoner();
		}
		
	}

}
