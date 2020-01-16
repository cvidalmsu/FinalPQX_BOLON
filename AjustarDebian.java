package main;

import helpers.ProductManager;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;

import es.us.isa.Choco.fmdiag.ChocoFMDiag;
import es.us.isa.Choco.fmdiag.ChocoMaxConfigurationFMDIAG;
import es.us.isa.Choco.fmdiag.configuration.ChocoBOLONExtendsConfiguration;
import es.us.isa.Choco.fmdiag.configuration.ChocoExplainErrorFMDIAG;
import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.questions.ChocoValidProductQuestion;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.models.FAMAfeatureModel.FAMAFeatureModel;
import es.us.isa.FAMA.models.FAMAfeatureModel.fileformats.XMLReader;
import es.us.isa.FAMA.models.FAMAfeatureModel.fileformats.XMLWriter;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.FAMA.models.variabilityModel.parsers.WrongFormatException;
import es.us.isa.FAMA.stagedConfigManager.Configuration;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.FAMA.models.FAMAfeatureModel.Feature;
import es.us.isa.FAMA.models.FAMAfeatureModel.Dependency;

import java.util.Iterator;

public class AjustarDebian {
	static ProductManager pman = new ProductManager();
	static FAMAFeatureModel fm;
	static String[] modelPath  = {"", ""};
	static XMLReader reader;
	
	public static void main(String[] args) throws Exception {

		
		XMLReader reader = new XMLReader();

		modelPath[0] = "Benchmarks/debian/xenialUTF.xml";
		modelPath[1] = "Benchmarks/debian/xenial-1.xml";
		
		fm = (FAMAFeatureModel) reader.parseFile(modelPath[0]);
		ajustarDebian();
		
			
	}
	
	static void ajustarDebian() throws Exception{
		ChocoReasoner reasoner = new ChocoReasoner();
		fm.transformTo(reasoner);

		ArrayList<Feature> features = (ArrayList<Feature>) fm.getFeatures();
		mensaje(0);
		
		ArrayList<String> delFeatures = new ArrayList<String>();
		delFeatures.add("e2fslibs(1.42.13-1ubuntu1)");
		
		while(delFeatures.size()>0){
			
			Feature ff = fm.searchFeatureByName(delFeatures.get(0));
			System.out.println(ff.getName());
		
			ff.removeAllRelations();
			ff.remove();
	
			mensaje(1);
	
			try{
				Feature ff2 = fm.searchFeatureByName("postfix(3.1.0-3)");
				System.out.println(ff2.getName());
			}catch(Exception ex){
				
			}
			
			Iterator<es.us.isa.FAMA.models.FAMAfeatureModel.Dependency> rel = fm.getDependencies();
			ArrayList<es.us.isa.FAMA.models.FAMAfeatureModel.Dependency> del = new ArrayList<es.us.isa.FAMA.models.FAMAfeatureModel.Dependency>();
		    features = (ArrayList<Feature>) fm.getFeatures();
			
			while (rel.hasNext()){
				es.us.isa.FAMA.models.FAMAfeatureModel.Dependency d1 = rel.next();
				
				Feature origen  = d1.getOrigin();
				Feature destino = d1.getDestination();
			
//				if (origen.getName().contains("postfix(3.1.0-3)") || destino.getName().contains("postfix(3.1.0-3)"))
//					System.out.println("Aquí!!!!!");
				
				if (!features.contains(origen) || !features.contains(destino))
					del.add(d1);
			} 
			
	//		mensaje(2);
			
			System.out.println("Dependencias a Borrar #" + del.size());
			int c=0;
			while(del.size()>0){
				System.out.println(del.get(0).getOrigin().getName() + " - " + del.get(0).getDestination().getName());
				fm.removeDependency(del.get(0));
				del.remove(0);
				c++;
			}
			System.out.println("Dependencias Borradas #" + c);
	
		
			mensaje(1);
			
			delFeatures.remove(0);
		}
		
		XMLWriter writer = new XMLWriter();
		writer.writeFile(modelPath[1], fm);		
	}	
	static void mensaje(int i){
		System.out.println("----");
//		System.out.println(fm.getFeatures());
		System.out.println(i + ". #Features: " + fm.getFeaturesNumber());
		System.out.println("----");
	}
	
}

/*
- mlterm-tools(3.5.0-1build1)
- anjuta-common(2:3.18.2-1)
- libcatalyst-actionrole-acl-perl(0.07-1)
- rt4-fcgi(4.2.12-5)
- qtcreator-plugin-go(3.5.0+15.10.20150812.1-0ubuntu2)
- 
- gtk-sharp2-gapi(2.12.10-6)
- plasma-widgets-addons(4:5.5.5-0ubuntu1)
- 

delFeatures.add("mono-dmcs(4.2.1.102+dfsg2-7ubuntu4)");
delFeatures.add("fusioninventory-agent-task-deploy(1:2.3.16-1)");
delFeatures.add("xserver-xorg-input-evdev(1:2.10.1-1ubuntu2)");
delFeatures.add("baloo(4:5.18.0-0ubuntu1)");
delFeatures.add("scim-pinyin(0.5.92-3build1)");
delFeatures.add("mlterm-tools(3.5.0-1build1)");
delFeatures.add("anjuta-common(2:3.18.2-1)");
delFeatures.add("libclosure-compiler-java-doc(20130227+dfsg1-8)");
delFeatures.add("gtk-sharp2-gapi(2.12.10-6)");
delFeatures.add("bitmap-mule(8.5+0.20030825.0433-16)");
delFeatures.add("exmh(1:2.8.0-5)");
delFeatures.add("courier-faxmail(0.68.2-1ubuntu7)");
delFeatures.add("mu-cite(8.1+0.20140609-1)");
delFeatures.add("python-sphinx-issuetracker(0.11-1)");
delFeatures.add("plasma-widgets-addons(4:5.5.5-0ubuntu1)");
delFeatures.add("python-launchpadlib(1.10.3-3)");
delFeatures.add("pkg-perl-tools(0.28)");
delFeatures.add("libconfig-model-dpkg-perl(2.076)");
delFeatures.add("libcatalyst-actionrole-acl-perl(0.07-1)");
delFeatures.add("rt4-fcgi(4.2.12-5)");
*/	
/*		delFeatures.add("perl-base(5.22.1-9)");
delFeatures.add("ibus-table-array30(1.8.2-1)");
delFeatures.add("pacemaker-cli-utils(1.1.14-2ubuntu1)");
delFeatures.add("libghc-haxr-dev(3000.11.1.2-1build1)");
delFeatures.add("python-oslo-db(4.7.0-2ubuntu1)");
delFeatures.add("python-schooltool.lyceum.journal(2.6.4-0ubuntu2)");
delFeatures.add("autogrid(4.2.6-3)");
delFeatures.add("kamailio-berkeley-modules(4.3.4-1.1ubuntu2)");
delFeatures.add("erlang-doc(1:18.3-dfsg-1ubuntu3)");
delFeatures.add("yorick-dev(2.2.04+dfsg1-5)");
delFeatures.add("python-zope.app.container(3.9.2-0ubuntu1)");
delFeatures.add("libghc-diagrams-lib-dev(1.3.0.8-1)");
delFeatures.add("libguestfs-perl(1:1.32.2-4ubuntu2)");
delFeatures.add("r-cran-boot(1.3-17-1)");
delFeatures.add("uwsgi(2.0.12-5ubuntu3)");
delFeatures.add("witty-doc(3.3.4+dfsg-6ubuntu1)");
delFeatures.add("mytharchive(2:0.28.0+fixes.20160413.15cf421-0ubuntu2)");
delFeatures.add("lgc-pg(1.3.1-1)");
delFeatures.add("tryton-client(3.8.4-1)");
delFeatures.add("ruby-passenger(5.0.27-2)");
delFeatures.add("vtk-examples(5.10.1+dfsg-2.1build1)");
delFeatures.add("bumblebee-nvidia(3.2.1-10)");
*/	
