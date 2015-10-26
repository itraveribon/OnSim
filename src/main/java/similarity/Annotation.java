package similarity;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.HashSet;
import java.util.Set;

import ontologyManagement.MyOWLOntology;
import ontologyManagement.OWLConcept;
import test.ComparisonResult;

public class Annotation {
	private OWLConcept c;
	private boolean notAnnotation;
	private String evidenceCode;
	
	public Annotation(OWLConcept con, String evidence, boolean not)
	{
		c = con;
		evidenceCode = evidence;
		notAnnotation = not;
	}
	
	public double similarity(Annotation b)
	{
		return c.similarity(b.c);
	}
	
	public String toString()
	{
		return c.getName();
	}
	
	public String getEvidenceCode()
	{
		return evidenceCode;
	}
	
	public boolean isNotAnnotation()
	{
		return notAnnotation;
	}
	
	public OWLConcept getOWLConcept()
	{
		return c;
	}
	
	public boolean equals(Annotation a)
	{
		//return c.equals(a.c) && notAnnotation == a.notAnnotation && evidenceCode.matches(a.evidenceCode);
		return c.equals(a.c);
	}
	
	public boolean equals(Object o)
	{
		if (o instanceof Annotation)
			return equals((Annotation) o);
		return false;
	}
	
	public int hashCode(){
		Boolean b = new Boolean(notAnnotation);
		return c.hashCode();// ^ b.hashCode() ^ evidenceCode.hashCode();
	}
	
}
