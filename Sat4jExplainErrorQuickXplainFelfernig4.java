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
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveAction;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.Semaphore;
import java.util.stream.Collectors;

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

public class Sat4jExplainErrorQuickXplainFelfernig4 extends Sat4jQuestion implements ValidConfigurationErrorsQuestion {
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

	public int lmax = 2;
	public int baseSize = 100;

	public Sat4jExplainErrorQuickXplainFelfernig4(int t) {
		this.m = 1;
		this.lmax = t;
		
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
	
	private ArrayList<List<String>> less(ArrayList<List<String>> aC, List<String> s2) {
		ArrayList<List<String>> res = new ArrayList<List<String>>(aC);
		res.remove(s2);
		return res;
	}


	private ArrayList<List<String>> lessS(ArrayList<List<String>> aC, ArrayList<List<String>> s2) {
		ArrayList<List<String>> res = new ArrayList<List<String>>(aC);
		
		res.removeAll(s2);
		return res;
	}

	private ArrayList<List<String>> plusS(ArrayList<List<String>> a1, ArrayList<List<String>> a2){
		ArrayList<List<String>> res = new ArrayList<List<String>>(a1);
		res.addAll(a2);
		
		return res;
	}

	private ArrayList<List<String>> plusS(ArrayList<List<String>> a1, List<String> a2){
		ArrayList<List<String>> res = new ArrayList<List<String>>(a1);
		res.add(a2);
		
		return res;
	}
	
	private ArrayList<List<String>> plusS(List<String> a1, ArrayList<List<String>> a2){
		ArrayList<List<String>> res = new ArrayList<List<String>>(a2);
		res.add(a1);
		
		return res;
	}

	private List<String> plus(ArrayList<List<String>> a1, ArrayList<List<String>> a2) {
		Set<String> res = new LinkedHashSet<>();
		
//		List<String> res = new ArrayList<String>();
		
		for(List<String> l1: a1){
			res.addAll(l1);
		}
		
		for(List<String> l2: a2){
			res.addAll(l2);
		}
		
		return(new ArrayList<String>(res));
	}

	private List<String> plus(ArrayList<List<String>> a1, List<String> a2) {
		Set<String> res = new LinkedHashSet<>(a2);
		
//		List<String> res = new ArrayList<String>();
		
		for(List<String> l2: a1){
			res.addAll(l2);
		}
		
		return(new ArrayList<String>(res));
	}

	private List<String> plus(List<String> a1, ArrayList<List<String>> a2) {
		Set<String> res = new LinkedHashSet<>(a1);
		
		for(List<String> l2: a2){
			res.addAll(l2);
		}
		
		return(new ArrayList<String>(res));
	}

	private List<String> less(List<String> aC, List<String> s2) {
		List<String> res = new ArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}

	private List<String> plus(List<String> a1, List<String> a2) {
		Set<String> res = new LinkedHashSet<>(a1);

		res.addAll(a2);
		return(new ArrayList(res));
	}

	public class AddCC extends RecursiveAction {
		Collection<String> AC;
		String kAC;
		
		public AddCC(Collection<String> AC) {
			this.AC = AC;
			ArrayList<String> sAC = new ArrayList<String>(AC);
			Collections.sort(sAC);
	
			this.kAC  = String.join(", ", sAC);			
			
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
		ForkJoinPool pool = new ForkJoinPool(16);
		//INCONSISTENT(plus(C, B))
		if (!INCONSISTENT(C, B, new ArrayList<String>()))
			return new ArrayList<String>();
		
		else if (C.isEmpty())
			return new ArrayList<String>();
		
		else
			return QX(C, B, new ArrayList<String>());
	}

	public List<String> QX(List<String> C, List<String> B, List<String> Bd) throws InterruptedException {
		if (Bd.size() != 0 && INCONSISTENT(C, B, Bd)) {
		//if (Bd.size() != 0 && INCONSISTENT(null, B, null)) {

			return new ArrayList<String>();
		}
		if (C.size() == 1) {
			return C;
		}
		
		int k = C.size() / 2;
		List<String> Ca = C.subList(0, k);
		List<String> Cb = C.subList(k, C.size());
		
		List<String> Delta2 = QX(Ca, plus(B, Cb), Cb);
		List<String> Delta1 = QX(Cb, plus(B, Delta2), Delta2);

		return plus(Delta1, Delta2);
	}

	public class QXGen extends RecursiveAction {
		/**
		 * 
		 */
		private static final long serialVersionUID = -7020044729656947296L;
		ArrayList<List<String>> C;
		ArrayList<List<String>> Bd;
		ArrayList<List<String>> B;
		ArrayList<List<String>> Delta;
		int  l;
			
		public QXGen(ArrayList<List<String>> C, ArrayList<List<String>> Bd, 
				     ArrayList<List<String>> B, ArrayList<List<String>> Delta, int l) {
			this.C = C;
			this.Bd = Bd;
			this.B = B;
			this.Delta = Delta;
			this.l = l;
		}

		public void compute() {	
			if (l < lmax){		
				if (Delta.size() != 0){
					AddCC cc0 = new AddCC(plus(Bd, B));
					pool.execute(cc0);
				}
				
				//////Bd U B assumed consistent
				ArrayList<List<String>> C1 = new ArrayList<List<String>>();
				C1.add(C.get(C.size()-1));
								
				if (C1.get(0).size() == 1 && Bd.size() != 0){
					QXGen qxGen1 = new QXGen(Bd, new ArrayList<List<String>>(), plusS(B, C1), C1, l + 1);
					pool.execute(qxGen1);
				
				}else if (C1.get(0).size() > 1){
					int kc = C1.size() / 2;
					ArrayList<List<String>> Ca = new ArrayList<List<String>>(); 
					Ca.add(C1.get(0).subList(0, kc));
					ArrayList<List<String>> Cb = new ArrayList<List<String>>(); 
					Cb.add(C1.get(0).subList(kc, C.size()));
			
					QXGen qxGen2 = new QXGen(Ca, plusS(Cb, Bd), B, Cb, l + 1);
					pool.execute(qxGen2);
				}
				
				/////Bd U B assumed inconsistent	
				if (Bd.size() != 0){	
					ArrayList<List<String>> Bd1 = new ArrayList<List<String>>(); 
					Bd1.add(Bd.get(Bd.size()-1));
					
					QXGen qxGen3 = new QXGen(Bd1, lessS(Bd, Bd1), B, new ArrayList<List<String>>(), l + 1);
					pool.execute(qxGen3);
				}
			}
		}
	}

	Boolean firstCase = true;
	private boolean INCONSISTENT(List<String> C, List<String> B, List<String> Bd) throws InterruptedException {
//		System.out.println("--D: " + D + ": " + D.size() + " -- S: " + S + ": " + S.size());
//		System.out.println("--AC: " + aC + ": " + aC.size() + "\n");
		
		cuantosCC++;
		Collections.sort(B);
		String kB = String.join(", ", B);
		
		CCValue CCres = LookUp.get(kB);
				
		if (CCres != null){
			CCres.mutex.acquire();

			cuantosSC++;
			return !CCres.val;
		}
		
		////////////////Previous Consistency Check Doesn't Exist!		
		ArrayList<List<String>> Cs  = new ArrayList<List<String>>(); Cs.add(C);
		ArrayList<List<String>> Bds = new ArrayList<List<String>>(); Bds.add(Bd);
		ArrayList<List<String>> Bs  = new ArrayList<List<String>>(); Bs.add(less(B, Bd));
		ArrayList<List<String>> Ds  = new ArrayList<List<String>>(); Ds.add(B);
		////
	
		QXGen tR = new QXGen(Cs, Bds,  Bs, Ds, 0);
		pool.execute(tR);
		
		Boolean res;
		
		if (firstCase){
			res = isConsistent(plus(B, C));
			firstCase= false;
		}else{
			res = isConsistent(B);
		}
	
		LookUp.put(kB, new CCValue(res, 1));
			
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