package similarity.matching;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.Set;

import ontologyManagement.OWLConcept;
import ontologyManagement.OWLLink;
import similarity.ComparableElement;
import test.OWLConceptComparison;

public class AnnSim {
	ComparableElement[] v1, v2;
	double[][] costMatrix;
	int[] assignment;
	Map<OWLConceptComparison,Double> mapComparisons = null;
	
	public AnnSim()
	{
		//map = new HashMap<ComparableElement,ComparableElement>();
	}
	
	public AnnSim(Map<OWLConceptComparison, Double> matrix)
	{
		mapComparisons = matrix;
	}
		
	public <T> double matching(Set<T> a, Set<T> b, OWLConcept orig, OWLConcept des) throws Exception
	{
		if (a.getClass() != b.getClass() && a != Collections.emptySet() && b != Collections.emptySet())// || !(a instanceof Set<ComparableElement>)))// || !(a instanceof Set<ComparableElement>))
			throw new Exception("Invalid comparison between " + a.getClass() + " " + b.getClass());
		else
		{
			if (a.equals(b))
				return 1.0;
			if (a.isEmpty() || b.isEmpty()) //Here we know that, almost one of the set is not empty
				return 0.0;
			costMatrix = new double [a.size()][b.size()];
			v1 = a.toArray(new ComparableElement[a.size()]);
			v2 = b.toArray(new ComparableElement[b.size()]);
			if (mapComparisons == null)
			{
				for (int i = 0; i< v1.length; i++)
				{
					ComparableElement s1 = v1[i];
					for (int j = 0; j < v2.length; j++)
					{
						ComparableElement s2 = v2[j];
						costMatrix[i][j] = 1 - s1.similarity(s2,orig,des); //The hungarian algorithm minimize. Therefore we convert the similarity in distance
					}
				}
			}
			else
			{
				for (int i = 0; i< v1.length; i++)
				{
					ComparableElement s1 = v1[i];
					for (int j = 0; j < v2.length; j++)
					{
						ComparableElement s2 = v2[j];
						costMatrix[i][j] = 1 - mapComparisons.get(new OWLConceptComparison((OWLConcept)s1, (OWLConcept) s2)); //The hungarian algorithm minimize. Therefore we convert the similarity in distance
					}
				}
			}
			//double startTime, estimatedTime, totalEstimatedTime;
			
			//startTime = System.nanoTime(); 
			HungarianAlgorithm hungarn = new HungarianAlgorithm(costMatrix);
			assignment = hungarn.execute();
			/*estimatedTime = System.nanoTime() - startTime;
			totalEstimatedTime = estimatedTime/1000000;
			System.out.println(totalEstimatedTime);*/
			
			/*startTime = System.nanoTime(); 
			Pseudoflow psFlow = new Pseudoflow(costMatrix);
			int[] assignment1 = psFlow.execute();
			estimatedTime = System.nanoTime() - startTime;
			totalEstimatedTime = estimatedTime/1000000;
			System.out.println(totalEstimatedTime);*/
			
			
			/*startTime = System.nanoTime(); 
			SSP ssp = new SSP(costMatrix);
			int[] assignment1 = ssp.execute();
			estimatedTime = System.nanoTime() - startTime;
			totalEstimatedTime = estimatedTime/1000000;
			System.out.println(totalEstimatedTime);
			
			*/
			
			/*startTime = System.nanoTime(); 
			SSPJGrapht sspJ = new SSPJGrapht(costMatrix);
			assignment1 = sspJ.execute();
			estimatedTime = System.nanoTime() - startTime;
			totalEstimatedTime = estimatedTime/1000000;
			System.out.println(totalEstimatedTime);*/
			
			/*startTime = System.nanoTime(); 
			HungarianAlgorithmSlow slow = new HungarianAlgorithmSlow(costMatrix);
			assignment1 = slow.execute();
			estimatedTime = System.nanoTime() - startTime;
			totalEstimatedTime = estimatedTime/1000000;
			System.out.println(totalEstimatedTime);*/
			
			double sim = 0, den = 0;
			for (int i = 0; i < assignment.length; i++)
			{
				int aux = assignment[i];
				//System.out.println(v1[i]);
				if (aux >=0) //If there is an assignment
				{
					//System.out.println(v2[aux]);
					//map.put(v1[i], v2[aux]);
					/*double print = 1-costMatrix[i][aux];
					
					double taxSim = ((OWLConcept) v1[i]).taxonomicSimilarity(((OWLConcept) v2[aux]));
					double neighSim = ((OWLConcept) v1[i]).similarityNeighbors((OWLConcept) v2[aux]);
					double icSim = ((OWLConcept) v1[i]).similarityIC((OWLConcept) v2[aux]);
					OWLConcept lca = ((OWLConcept) v1[i]).getLCA(((OWLConcept) v2[aux]));
					boolean printIf = false;
					if (neighSim > 0.25 && neighSim != 1)
					{
						Set<OWLLink> neighA =((OWLConcept) v1[i]).getNeighbors();
						for (OWLLink l: neighA)
						{
							if (l.getRelation().toString().matches("http://purl.org/obo/owl/obo#regulates"))
								printIf = true;
						}
						if (printIf)
						{
							Set<OWLLink> neighB =((OWLConcept) v2[aux]).getNeighbors();
							for (OWLLink l: neighB)
							{
								if (l.getRelation().toString().matches("http://purl.org/obo/owl/obo#negatively_regulates") || l.getRelation().toString().matches("http://purl.org/obo/owl/obo#positively_regulates"))
								{
									printIf = true;
									break;
								}
								printIf = false;
							}
						}
					}
					if (v1[i] instanceof OWLLink)
					{
						System.out.println(((OWLLink) v1[i]).getExplanations());
						System.out.println();
						System.out.println(((OWLLink) v2[aux]).getExplanations());
					}
					System.out.println(((OWLConcept) v1[i]).getName() + "\t" + ((OWLConcept) v2[aux]).getName() + "\t" + print + "\t" + taxSim + "\t" + neighSim + "\t" + icSim + "\t" + lca.getName());*/
					sim += 1-costMatrix[i][aux];
				}
			}
			
			/*double sim1 = 0;
			for (int i = 0; i < assignment1.length; i++)
			{
				int aux = assignment1[i];
				if (aux >=0) //If there is an assignment
				{
					double print = 1-costMatrix[i][aux];
					sim1 += 1-costMatrix[i][aux];
				}
			}
			if (sim != sim1)
			{
				System.out.println("Pay attention");
				System.out.println(sim + " " + sim1);
				for (int i = 0; i < assignment.length; i++)
					System.out.print(assignment[i] + "\t");
				System.out.println();
				for (int i = 0; i < assignment1.length; i++)
					System.out.print(assignment1[i] + "\t");
				System.out.println();
				psFlow = new Pseudoflow(costMatrix);
				assignment1 = psFlow.execute();
			}*/
			
			return 2*sim/(v1.length+v2.length);
		}
	}

}

