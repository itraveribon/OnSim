package test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
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
import ontologyManagement.OWLExplanation;
import ontologyManagement.OWLLink;
import similarity.Annotation;
import similarity.matching.AnnSim;
import similarity.matching.BipartiteGraphMatching;

public class DatasetTest {
	
	/*public static Map<OWLConcept, Map<OWLConcept, Integer>> getComparisonMap(List<ComparisonResult> comparisons, MyOWLOntology o)
	{
		Map<OWLConcept, Map<OWLConcept, Integer>> owlConceptComparisons = new HashMap<OWLConcept, Map<OWLConcept, Integer>>();
		for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
		{
			ComparisonResult comp = i.next();
			Set<OWLConcept> a = getConceptAnnotations(comp.getConceptA(), "src/main/resources/dataset3/cellular_annt", o);
			Set<OWLConcept> b = getConceptAnnotations(comp.getConceptB(), "src/main/resources/dataset3/cellular_annt", o);
			for (Iterator<OWLConcept> j = a.iterator(); j.hasNext();)
			{
				OWLConcept c = j.next();
				if (owlConceptComparisons.get(c) == null)
				{
					owlConceptComparisons.put(c, new HashMap<OWLConcept, Integer>());
				}
				Map<OWLConcept, Integer> pairsA = owlConceptComparisons.get(c);
				for (Iterator<OWLConcept> k = b.iterator(); k.hasNext();)
				{
					OWLConcept d = k.next();
					if (pairsA.get(d) == null)
					{
						pairsA.put(d, 0);
					}
					pairsA.put(d, pairsA.get(d) + 1);
					if (owlConceptComparisons.get(d) == null)
					{
						owlConceptComparisons.put(d, new HashMap<OWLConcept, Integer>());
					}
					if (c != d)
					{
						Map<OWLConcept, Integer> pairsB = owlConceptComparisons.get(d);
						if (pairsB.get(c) == null)
						{
							pairsB.put(c, 0);
						}
						pairsB.put(c, pairsB.get(c) + 1);
					}
				}
			}
		}
		return owlConceptComparisons;
	}*/
	
	
	public static Map<OWLConcept, Integer> getComparisonMap(List<ComparisonResult> comparisons, MyOWLOntology o)
	{
		Map<OWLConcept, Integer> owlConceptComparisons = new HashMap<OWLConcept, Integer>();
		//String[] files = {"src/main/resources/dataset3/cellular_annt", "src/main/resources/dataset3/molecularFunction_annt", "src/main/resources/dataset3/process_annt"};
		String[] files = {"src/main/resources/dataset3/process_annt"};
		for (String file:files)
		{
			for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
			{
				ComparisonResult comp = i.next();
				Set<OWLConcept> a = getConceptAnnotations(comp.getConceptA(), file, o, true);
				Set<OWLConcept> b = getConceptAnnotations(comp.getConceptB(), file, o, true);
				for (Iterator<OWLConcept> j = a.iterator(); j.hasNext();)
				{
					OWLConcept c = j.next();
					if (owlConceptComparisons.get(c) == null)
					{
						owlConceptComparisons.put(c, 0);
					}
					owlConceptComparisons.put(c, owlConceptComparisons.get(c) + 1);
				}
				for (Iterator<OWLConcept> j = b.iterator(); j.hasNext();)
				{
					OWLConcept c = j.next();
					if (owlConceptComparisons.get(c) == null)
					{
						owlConceptComparisons.put(c, 0);
					}
					owlConceptComparisons.put(c, owlConceptComparisons.get(c) + 1);
				}
			}
		}
		return owlConceptComparisons;
	}
	
	public static void updateComparisonMap(Set<OWLConcept> a, Set<OWLConcept> b, Map<OWLConcept, Integer> owlConceptComparisons)
	{
		for (Iterator<OWLConcept> i = a.iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			owlConceptComparisons.put(c, owlConceptComparisons.get(c) - 1);
		}
		for (Iterator<OWLConcept> i = b.iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			owlConceptComparisons.put(c, owlConceptComparisons.get(c) - 1);
		}
	}
	
	public static void freeMemory (Map<OWLConcept, Integer> owlConceptComparisons, MyOWLOntology o)
	{
		Set<OWLConcept> removable = new HashSet<OWLConcept>();
		for (Iterator<OWLConcept> i = owlConceptComparisons.keySet().iterator(); i.hasNext();)
		{
			OWLConcept c = i.next();
			if (owlConceptComparisons.get(c) == 0)
			{
				o.removeConcept(c);
				removable.add(c);
			}
		}
		for (Iterator<OWLConcept> i = removable.iterator(); i.hasNext();)
			owlConceptComparisons.remove(i.next());
	}
	
	public static Set<OWLConcept> getOntologyTerms(List<ComparisonResult> comparisons, String[] files, MyOWLOntology o)
	{
		Set<String> proteins = new HashSet<String>();
		Set<OWLConcept> anns = new HashSet<OWLConcept>();
		for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
		{
			ComparisonResult cR = i.next();
			proteins.add(cR.getConceptA());
			proteins.add(cR.getConceptB());
		}
		for (Iterator<String> i = proteins.iterator(); i.hasNext();)
		{
			String p = i.next();
			for (String file:files)
			{
				anns.addAll(DatasetTest.getConceptAnnotations(p, file, o, true));
			}
		}
		return anns;
	}
	
	public static void main (String[] args) throws Exception
	{
		Map<String, String> ontPrefix = new HashMap<String,String>();
		ontPrefix.put("src/main/resources/dataset3/", "http://purl.org/obo/owl/GO#");
		ontPrefix.put("src/main/resources/dataset32014/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2008/", "http://purl.org/obo/owl/GO#");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2010/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2012/", "http://purl.obolibrary.org/obo/");
		ontPrefix.put("src/main/resources/DILS2015/annt_goa_2014/", "http://purl.obolibrary.org/obo/");
		String[] p = {"src/main/resources/dataset3/"};
		for (String prefix: p)
		{
			String ontFile = prefix + "goProtein/goEL.owl";
			MyOWLOntology o = new MyOWLOntology(ontFile, ontPrefix.get(prefix));
			String comparisonFile = prefix + "proteinpairs.txt";
			List<ComparisonResult> comparisons = readComparisonFile(comparisonFile);
			//String[] files = {"src/main/resources/dataset3/cellular_annt", "src/main/resources/dataset3/molecularFunction_annt", "src/main/resources/dataset3/process_annt"};
			String[] files = {prefix + "bp"};
			
			
			/*double startRelTime = System.nanoTime();
			Set<OWLConcept> anns = getOntologyTerms(comparisons, files, o);
			o.setOWLLinks(anns);
			double estimatedRelTime = (System.nanoTime() - startRelTime)/1000000;
			System.out.println(estimatedRelTime/1000/60);*/
			PrintWriter generalWriter = new PrintWriter(prefix + "results.txt", "UTF-8");
			//generalWriter.println("Protein1\tProtein2\tSimilarity");
			int counter = 0, total = comparisons.size();
			for (Iterator<ComparisonResult> i = comparisons.iterator(); i.hasNext();)
			{
				ComparisonResult comp = i.next();
				double sim = 0;
				double totalEstimatedTime = 0;
				for (String file:files)
				{
					Set<OWLConcept> a = getConceptAnnotations(comp.getConceptA(), file, o, true);
					Set<OWLConcept> b = getConceptAnnotations(comp.getConceptB(), file, o, true);
					double startTime = System.nanoTime();  
					AnnSim bpm = new AnnSim();
					double aux = bpm.matching(a, b, null, null);
					double estimatedTime = System.nanoTime() - startTime;
					totalEstimatedTime += estimatedTime/1000000;
					sim += aux;
				}
				comp.setSimilarity(sim/files.length);
				System.out.println(comp + "\t" + totalEstimatedTime + "\t" + counter++ + "/" + total);
				generalWriter.println(comp + "\t" + totalEstimatedTime);
			}
			generalWriter.close();
			//System.out.println(estimatedRelTime);
			o.disposeReasoner();
		}
		
	}
	
	public static List<ComparisonResult> readComparisonFile(String comparisonFile)
	{
		List<ComparisonResult> comparisons = new ArrayList<ComparisonResult>();
		
		InputStream    fis;
		BufferedReader br;
		String         line;
		
		try {
			fis = new FileInputStream(comparisonFile);
			br = new BufferedReader(new InputStreamReader(fis, Charset.forName("UTF-8")));
			while ((line = br.readLine()) != null) {
			    String[] elements = line.split("\t");
			    comparisons.add(new ComparisonResult(elements[0], elements[1]));
			}

			// Done with the file
			br.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return comparisons;
	}
	
	private static Set<File> getFiles(File f)
	{
		File[] files = f.listFiles();
		Set<File> setFile = new HashSet<File>();
		for (int i = 0; i < files.length; i++)
		{
			if (files[i].isDirectory())
			{
				setFile.addAll(getFiles(files[i]));
			}
			else
				setFile.add(files[i]);
		}
		return setFile;
	}
	
	public static Set<OWLConcept> getConceptAnnotations(String conceptName, String folder, MyOWLOntology o, boolean iea)
	{
		File f = new File(folder + "/" + conceptName);
		if (f.exists())
			return getAnnotations(f,o, iea);
		
		return new HashSet<OWLConcept>();
	}
	
	public static Set<OWLConcept> getAnnotations(File f, MyOWLOntology o, boolean iea)
	{
		InputStream    fis;
		BufferedReader br;
		String         line;
		
		Set<OWLConcept> annotations = new HashSet<OWLConcept>();
		
		try {
			fis = new FileInputStream(f);
			br = new BufferedReader(new InputStreamReader(fis, Charset.forName("UTF-8")));
			line = br.readLine(); //First line contains the number of annotations
			int numAnnotations = Integer.parseInt(line);
			for (int i = 0; i < numAnnotations; i++){
				line = br.readLine();
				String term = line.split("\t")[0];
				String evidence = "KKK";//line.split("\t")[1];
				
				/*String notAnn = line.split("\t")[2];
				boolean not = false;
				if (!notAnn.isEmpty())
					not = true;*/
			    //String element = "http://purl.org/obo/owl/GO#" + line.replace(":", "_");
				//String element = "http://purl.obolibrary.org/obo/" + line.replace(":", "_");
				if (iea || (!iea && !evidence.matches("IEA"))) 
				{
					String element = o.getOntologyPrefix() + term.replace(":", "_");
					OWLConcept c = o.getOWLConcept(element);
					if (c != null)
						annotations.add(c);
				}
			   // Annotation a = new Annotation(c, evidence, not);
			}

			// Done with the file
			br.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return annotations;
	}
	

}
