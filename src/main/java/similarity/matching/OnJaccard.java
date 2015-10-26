package similarity.matching;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import ontologyManagement.OWLConcept;
import similarity.ComparableElement;
import test.OWLConceptComparison;

public class OnJaccard {

	ComparableElement[] v1, v2;
	double[][] costMatrix;
	int[] assignment;
	Map<OWLConceptComparison,Double> mapComparisons = null;
	
	public OnJaccard()
	{
		//map = new HashMap<ComparableElement,ComparableElement>();
	}
	
	public OnJaccard(Map<OWLConceptComparison, Double> matrix)
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
						costMatrix[i][j] = s1.similarity(s2,orig,des); //The hungarian algorithm minimize. Therefore we convert the similarity in distance
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
						costMatrix[i][j] = mapComparisons.get(new OWLConceptComparison((OWLConcept)s1, (OWLConcept) s2)); //The hungarian algorithm minimize. Therefore we convert the similarity in distance
					}
				}
			}
			double sim = 0;
			for (int i = 0; i < v1.length; i++)
			{
				double maxRow = 0;
				for (int j = 0; j < v2.length; j++)
				{
					if (maxRow < costMatrix[i][j])
						maxRow = costMatrix[i][j];
				}
				sim += maxRow;
			}
			
			for (int j = 0; j < v2.length; j++)
			{
				double maxCol = 0;
				for (int i = 0; i < v1.length; i++)
				{
					if (maxCol < costMatrix[i][j])
						maxCol = costMatrix[i][j];
				}
				sim += maxCol;
			}
			return sim / (a.size() + b.size());
		}
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

}
