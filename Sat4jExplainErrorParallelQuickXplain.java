package es.us.isa.Sat4j.fmdiag;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.less;
import static es.us.isa.Sat4j.fmdiag.DiagHelpers.plus;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.OptionalInt;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveAction;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.Semaphore;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ValidConfigurationErrorsQuestion;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.Sat4jReasoner.Sat4jQuestion;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.Sat4jReasoner.Sat4jResult;

public class Sat4jExplainErrorParallelQuickXplain extends Sat4jQuestion implements ValidConfigurationErrorsQuestion {
	String cnf_content = "c CNF file\n"; String clauses="";
	List<RecursiveTask<Boolean>> forks;
	
	public HashMap<String, String> result = new HashMap<String, String>();

	Map<String, String> relations = null;
	public boolean flexactive = false;
	public int m = 1;
	private Sat4jReasoner reasoner;

	Product s, r;

	class CCValue{
		public Boolean val;
		public Integer state;
		public Semaphore mutex;
		
		CCValue(Boolean val, Integer state){
			this.val = val;
			this.state = state;
			mutex = new Semaphore(0);
		}		
	}
		
	public Integer cuantosCC = 0; //Cuantos consistency checking
	public Integer cuantosSC  = 0; //Cuantos useful speculative 
	
	/*Map Consistency*/
	public ConcurrentMap<String, CCValue> LookUp = new ConcurrentHashMap<String, CCValue>();
	/*---------------*/
	ForkJoinPool pool = new ForkJoinPool();
	
	public long sizeCM(){
		return LookUp.size();
	}
	
	public void setConfiguration(Product s) {
		this.s = s;
	}

	public void setRequirement(Product r) {
		this.r = r;
	}

	public int numberOfLevels = 2;
	public int baseSize = 100;

	public Sat4jExplainErrorParallelQuickXplain(int t) {
		this.m = 1;
		this.numberOfLevels = t;
		
		cuantosCC=0;
		cuantosSC=0;
	}

	public PerformanceResult answer(Reasoner r) throws FAMAException, InterruptedException {
		reasoner = (Sat4jReasoner) r;
		// solve the problem y fmdiag
		relations = new HashMap<String, String>();

		Map<String, String> productConstraint = new HashMap<String, String>();
		ArrayList<String> feats = new ArrayList<String>();
		for (GenericFeature f : this.s.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			String name = "U_" + f.getName();
			productConstraint.put(name, cnfVar + " 0");
			feats.add(name);
		}

		int cindex = 0;
		for (String cl : reasoner.clauses) {
			relations.put(cindex + "rel", cl);
			cindex++;
		}
		
		relations.putAll(productConstraint);	

		// First we create the content of the cnf file that's to be used by the consistent function
		// We show as comments the variables's number
		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName + "\n";
		}
		
		for (String cons : reasoner.clauses) {
			clauses += (String) cons + "\n";
		}
				
		List<String> C = new ArrayList<String>(feats);
		List<String> B = new ArrayList<String>(relations.keySet());

		List<String> quickX = QuickXplain(C, less(B, C));
		for (String s : quickX) {
			result.put(s, productConstraint.get(s));
		}
		
		return new Sat4jResult();
	}
	
	private List<String> less(List<String> aC, List<String> s2) {
		List<String> res = new ArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}

	private List<String> plus(List<String> a1, List<String> a2) {
		List<String> res = new ArrayList<String>();
		res.addAll(a2);
		res.addAll(a1);
		return res;
	}

	public class AddConsistencyCheck extends RecursiveAction {
		Collection<String> AC;
		String kAC;
		
		public AddConsistencyCheck(Collection<String> AC) {
			this.AC = AC;
			//sort sAC
//			ArrayList<String> sAC = new ArrayList<String>(AC);
//			Collections.sort(sAC);
			//
			this.kAC  = String.join(", ", this.AC);			
			LookUp.putIfAbsent(kAC, new CCValue(false, 0));
		}
			
		public void compute() {	
			CCValue cc = LookUp.get(kAC);
			if (LookUp.get(kAC).state==0){
				cc.state = 1;
				cc.val = isConsistent(AC);
				cc.mutex.release();
			}
		}
	}

	public List<String> QuickXplain(List<String> C, List<String> B) throws InterruptedException { 
//		System.out.println("C: " + C + " - " + isConsistent(C) + "\nB: " + B + " - " + isConsistent(B));
//		System.out.println("(B U C): " + plus(B,C) + " - " + isConsistent(plus(B,C)) + "\n");
	
		ForkJoinPool pool = new ForkJoinPool(16);
		
		if (!INCONSISTENT(C, B, new ArrayList<String>()))
			return new ArrayList<String>();
		
		else if (C.isEmpty())
			return new ArrayList<String>();
		
		else
			return QX(C, B, new ArrayList<String>());
	}

	public List<String> QX(List<String> C, List<String> B, List<String> D) throws InterruptedException {
//		System.out.println("QX--->\n" + "C: {" + C + "}\n" + "D: {" + D + "}: " + D.size() + "\nB: " + B + ": " + B.size() + " (" + isConsistent(B) + ")\n");
		
		if (D.size() != 0 && INCONSISTENT(C, B, D)) {
			return new ArrayList<String>();
		}
		if (C.size() == 1) {
			return C;
		}
		
		int k = C.size() / 2;
		List<String> C1 = C.subList(0, k);
		List<String> C2 = C.subList(k, C.size());
		
		List<String> D2 = QX(C1, plus(B, C2), C2);
		List<String> D1 = QX(C2, plus(B, D2), D2);

		return plus(D1, D2);
	}

	public class LookAheadFJ extends RecursiveAction {
		List<String> C;
		List<String> B;
		List<String> D;
		int  l;
			
		public LookAheadFJ(List<String> C, List<String> B, List<String> D, int l) {
			this.C = C;
			this.B = B;
			this.D = D;
			this.l = l;
		}

		public void compute() {	
//			System.out.println("C: " + C + "(" + C.size() + ")\nB: " + B + "(" + B.size() + ")\nD: " + D + "(" + D.size() + ")\n");
			
			////1st Base Case
			if (l > numberOfLevels)
			    return;
						
			Integer Cs=C.size();
			Integer Ds=D.size();
			
			///////Assumed 1st Base Case False (B IS CONSISTENT)
			if (Cs == 1){
				List<String> B0 = plus(less(B, D), C); 
				AddConsistencyCheck cc0 = new AddConsistencyCheck(B0);
				pool.execute(cc0);	
			
			}else if (Cs > 1){
				int kc = Cs / 2;
				List<String> C1 = C.subList(0, kc);
				List<String> C2 = C.subList(kc, Cs);
		
				List<String> B0 = plus(B, C2); 
				AddConsistencyCheck cc1 = new AddConsistencyCheck(B0);
				pool.execute(cc1);
						
				LookAheadFJ la0 = new LookAheadFJ(C1, B0, C2, l + 1);
				pool.execute(la0);
			}
			
			///////Assumed 1st Case True (B IS INCONSISTENT)
			if (Ds > 1){	
				int kd = Ds / 2;
				List<String> D1 = D.subList(0, kd);
				List<String> D2 = D.subList(kd, Ds);
							
				List<String> B1a = plus(less(B, D), D2); 
				List<String> B1b = new ArrayList<String>(B1a); 
				
				
				////2. Possibilities: Cs is a diagnosis or not!!!!! --> LookAhead in both cases...
				if (Cs==1){
					B1a = plus(B1a, C);
					AddConsistencyCheck cc3 = new AddConsistencyCheck(B1a);
					pool.execute(cc3);

					LookAheadFJ la1 = new LookAheadFJ(D1, B1a, D2, l + 1);
					pool.execute(la1);
				}
				
				AddConsistencyCheck cc4 = new AddConsistencyCheck(B1b);
				pool.execute(cc4);
							
				LookAheadFJ la2 = new LookAheadFJ(D1, B1b, D2, l + 1);
				pool.execute(la2);
			}	
		}
	} 

	Boolean firstCase = true;
	private boolean INCONSISTENT(List<String> C, List<String> B, List<String> D) throws InterruptedException {
		
//		System.out.println("--D: " + D + ": " + D.size() + " -- S: " + S + ": " + S.size());
//		System.out.println("--AC: " + aC + ": " + aC.size() + "\n");
		
		cuantosCC++;
//		Collections.sort(B);
		String kB = String.join(", ", B);
		CCValue CCres = LookUp.get(kB);
				
		if (CCres != null){
			CCres.mutex.acquire();
		
			cuantosSC++;
			return !CCres.val;
		}
		
		//LookAhead(C, B, D, 1);		
		LookAheadFJ tR = new LookAheadFJ(C, B,  D, 1);
		pool.execute(tR);
			
		Boolean res=false;
		
		if (firstCase){
			/*kB = String.join(", ", plus(B, C));
			
			AddConsistencyCheck cc1 = new AddConsistencyCheck(plus(B, C));
			pool.execute(cc1);	
			
			CCres = LookUp.get(kB);
			
			if (CCres != null){
				CCres.mutex.acquire();				
			}
			*/
			res = isConsistent(plus(B,C));
			firstCase= false;
		}else{
			/*AddConsistencyCheck cc1 = new AddConsistencyCheck(B);
			pool.execute(cc1);
		
			CCres = LookUp.get(kB);
			
			if (CCres != null){
				CCres.mutex.acquire();				
			}*/
			res = isConsistent(B);
		}
				
		return !res;		
	}

	private boolean isConsistent(Collection<String> aC) {

		/* Increment Step*/
		//step.increment();
		//System.out.println("**Step: " + step.value);

		// Start the problem
		String cnf_content=new String(this.cnf_content);
		cnf_content += "p cnf " + reasoner.variables.size() + " " + (aC.size()+reasoner.clauses.size()) + "\n";
	
//		cnf_content+=clauses;
		// Configuration clauses
		for (String cons : aC) {
			cnf_content += (String) relations.get(cons) + "\n";

		}

		cnf_content+=clauses;
		// End file
		//cnf_content += "0";
		ByteArrayInputStream stream = new ByteArrayInputStream(cnf_content.getBytes(StandardCharsets.UTF_8));

		ISolver s = SolverFactory.newDefault();
		Reader reader = new DimacsReader(s);
		try {
			reader.parseInstance(stream);
			//System.out.println(cnf_content);
			return s.isSatisfiable();
		} catch (TimeoutException | ParseFormatException | ContradictionException | IOException e) {
			//e.printStackTrace();

		}
		return false;

	}
	
	@Override
	public void setProduct(Product p) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isValid() {
		// TODO Auto-generated method stub
		return false;
	}
}