package ws.prova.reference2.builtins;

import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;

import org.apache.log4j.Logger;

import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.RDFNode;

import ws.prova.agent2.ProvaReagent;
import ws.prova.kernel2.ProvaConstant;
import ws.prova.kernel2.ProvaDerivationNode;
import ws.prova.kernel2.ProvaGoal;
import ws.prova.kernel2.ProvaKnowledgeBase;
import ws.prova.kernel2.ProvaList;
import ws.prova.kernel2.ProvaLiteral;
import ws.prova.kernel2.ProvaObject;
import ws.prova.kernel2.ProvaPredicate;
import ws.prova.kernel2.ProvaRule;
import ws.prova.kernel2.ProvaVariable;
import ws.prova.kernel2.ProvaVariablePtr;
import ws.prova.reference2.ProvaConstantImpl;
import ws.prova.reference2.ProvaListImpl;
import ws.prova.reference2.ProvaLiteralImpl;
import ws.prova.reference2.ProvaRuleImpl;

public class ProvaSparqlSelectImpl extends ProvaBuiltinImpl {

	private static Logger log = Logger.getLogger(ProvaSparqlSelectImpl.class);
	
	public ProvaSparqlSelectImpl(ProvaKnowledgeBase kb) {
		super(kb, "sparql_select");
	}
	
	@Override
	public int getArity() {
		return 3;
	}
	
	@Override
	public boolean process(ProvaReagent prova, ProvaDerivationNode node,
			ProvaGoal goal, List<ProvaLiteral> newLiterals, ProvaRule query) {
		List<ProvaVariable> variables = query.getVariables();
		ProvaLiteral literal = goal.getGoal();
		ProvaList terms = (ProvaList) literal.getTerms();
		ProvaObject[] data = terms.getFixed();
		
		// Check that there are at least two parameter
		if(data.length <= 1) {
			// No query given means false, no variable/constant means true.
			if(data.length == 0) {
				if(log.isDebugEnabled())
					log.debug("Syntax error. First parameter should be a string (select query).");
				return false;
			}
			return true;
		}
				
		// Create a SparqlQuery instance
		JenaSparqlQuery jsq = processTerms(terms, variables);
		if(jsq == null)
			return false;
		
		// If the second parameter (request Id) is not bound, assign it now.
		Long id = new Long(0);
		ProvaObject oid = resolve(data[1], variables);
		if(!(oid instanceof ProvaConstant)) {
			Random r = new Random(System.currentTimeMillis()); 
			id = r.nextLong();
		} else {
			// TODO: Maybe remove all clauses matching (Id, x, x, ...) from sparql_results
			// clauseSet.
			id = (Long) ((ProvaConstant) oid).getObject();
		}
		

		
		boolean ok;
		
		// Create a new nameless predicate
		ProvaPredicate pred = kb.getOrGeneratePredicate("sparql_results", jsq.getArity() + 1);
		
		if(jsq.isAsk()) {
			try {
				// Execute ASK query
				boolean result = jsq.executeAsk();
				ok = true;
				
				// If positive answer, add sparql_results(Id) fact to knowledge base.
				if(result) {
					ProvaList ls = ProvaListImpl.create(new ProvaObject[] {ProvaConstantImpl.create(id)});
					ProvaLiteral lit = new ProvaLiteralImpl(pred, ls);
					ProvaRule clause = ProvaRuleImpl.createVirtualRule(1, lit, null);
					pred.addClause(clause);
				}
				
			} catch (Exception e) {
				if(log.isDebugEnabled())
					log.debug("Error while executing query: ", e);
				ok = false;
			}
		} else {		
			try {
				// Execute SELECT query
				ResultSet results = jsq.executeSelect();

				// Process the results (moved to another function for readability)
				ok = processResults(results, data, pred, variables, id);
			} catch (Exception e) {
				if(log.isDebugEnabled())
					log.debug("Error while executing query: ", e);
				ok = false;
			}
		}
		
		// Close the stream.
		jsq.destroy();
		
		return ok;
	}

	protected JenaSparqlQuery processTerms(ProvaList terms, List<ProvaVariable> variables) {
		ProvaObject[] data = terms.getFixed();
			
		// First parameter contains the sparql query.
		ProvaObject query_term = resolve(data[0], variables);
		
		// If it isn't a ProvaConstant, stop processing.
		if(!(query_term instanceof ProvaConstant)) {
			if(log.isDebugEnabled())
				log.debug("Syntax error. First parameter should be a string (sparql query).");
			return null;
		}
		
		// Get string out of constant
		String query_string = ((ProvaConstant) query_term).toString();
		
		// Optional third parameter can contain a list of variables to replace in query
		if(data.length >= 3) {
			ProvaObject l = data[2];
			if(!(l instanceof ProvaList)) {
				if(log.isDebugEnabled())
					log.debug("Error: third term should be a list.");
				return null;
			}
			ProvaObject[] query_replacements = ((ProvaList) l).getFixed();
			
			for(ProvaObject replace : query_replacements) {
				replace = resolve(replace, variables);
				
				if(replace instanceof ProvaList) {
					ProvaObject[] replace_data = ((ProvaList) replace).getFixed();
					
					// Second term can also be a (bound) variable
					replace_data[1] = resolve(replace_data[1], variables);
					
					if(!((replace_data[0] instanceof ProvaConstant) && (replace_data[1] instanceof ProvaConstant)))  {
						if(log.isDebugEnabled())
							log.debug("Syntax error: Inner list in replacement list must have the form 'var(Var)'.");
						return null;
					}
					
					// Get variable to replace and prefix it with '?'
					String variable = "$" + ((ProvaConstant) replace_data[0]).toString();
					
					// Get replacement
					String value = ((ProvaConstant) replace_data[1]).toString();
					
					// Replace in query
					query_string = query_string.replaceAll(Matcher.quoteReplacement(variable), Matcher.quoteReplacement(value));
					
				} else {
					if(log.isDebugEnabled())
						log.debug("Syntax error: Found a element in replacement list which is not a ProvaList.");
					return null;
				}
				
			}
		}
		
		// (optional) 4th parameter is the sparql endpoint (SERVICE)
		String service = null;
		if(data.length == 4) {
			ProvaObject o = resolve(data[3], variables);
			if((o instanceof ProvaConstant)) {
				service = o.toString();
			} else {
				if(log.isDebugEnabled())
					log.debug("Syntax error: 4th parameter must be constant (service string).");
				return null;
			}
		}
		
		if(log.isDebugEnabled())
			log.debug("Executing query:" + query_string);		
		
		return new JenaSparqlQuery(query_string, service);
	}
	
	protected boolean processResults(ResultSet results, ProvaObject[] data,
			ProvaPredicate pred, List<ProvaVariable> variables, Long id) {
			
		// Cycle through result set
		while (results.hasNext()) {
			QuerySolution solution = results.nextSolution();
			List<ProvaObject> terms_list = new LinkedList<ProvaObject>();
			
			// Add id as first term
			terms_list.add(ProvaConstantImpl.create(id));
			
			for(String var : results.getResultVars()) {
			
				// Extract the matching field from the solution.
				RDFNode rn = solution.get(var);
				if(rn == null) {
					if(log.isDebugEnabled())
						log.debug("No such result in the select query: " + var + ".");
					return false;
				}
				
				Object field = null;
				if(rn.isLiteral())
					field = rn.asLiteral().getValue();
				else
					field = rn.toString();
								
				
				// Add it to the list. Variables match anyway.
				terms_list.add(ProvaConstantImpl.create(field));
			}
			
			ProvaList ls = ProvaListImpl.create(terms_list);
			ProvaLiteral lit = new ProvaLiteralImpl(pred,ls);
			ProvaRule clause = ProvaRuleImpl.createVirtualRule(1, lit, null);
			pred.addClause(clause);
		}
		
		return true;
	}
	
	/*
	 * Little helper method to resolve ProvaVariables to the constants their bound to
	 */
	protected ProvaObject resolve(ProvaObject o, List<ProvaVariable> variables) {
		if(o instanceof ProvaVariablePtr) {
			ProvaVariablePtr varPtr = (ProvaVariablePtr) o;
			o = variables.get(varPtr.getIndex()).getRecursivelyAssigned();
		}
		return o;
	}

	protected static class JenaSparqlQuery {
		
		private String query;
		private String service;
		private Query jena_query;
		QueryExecution jena_query_execution;
			
		public JenaSparqlQuery(String q, String s) {
			query = q;
			service = s;
			jena_query = QueryFactory.create(query);
			
			if(service != null)
				jena_query_execution = QueryExecutionFactory.sparqlService(service, jena_query);
			else
				jena_query_execution = QueryExecutionFactory.create(jena_query);
		}	
		
		public int getArity() {
			if(isAsk()) {
				return 0;
			} else {
				return jena_query.getResultVars().size();
			}
		}
		
		public boolean isAsk() {
			return jena_query.isAskType();
		}

		public ResultSet executeSelect() {
			ResultSet results = jena_query_execution.execSelect();
			return results;
		}
		
		public boolean executeAsk() {
			boolean result = jena_query_execution.execAsk();
			return result;
		}
		
		public void destroy() {
			jena_query_execution.close();
		}
	}
}
