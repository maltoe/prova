package ws.prova.service;

import java.io.BufferedReader;
import java.io.PrintWriter;
import java.util.List;

import ws.prova.exchange.ProvaSolution;
import ws.prova.kernel2.ProvaList;

public interface ProvaService extends ProvaMiniService, EPService {

	public String instance(String agent, String rulebase);

	public void release(String id);

	public void init();

	public void destroy();

	public List<ProvaSolution[]> consult(String id, String src, String key);

	public void send(String dest, ProvaList terms);

	public void setGlobalConstant(String agent, String name, Object value);

	public List<ProvaSolution[]> consult(String agent, BufferedReader in,
			String key);
	
	public void unconsult(String agent, String key);

	public void register(String agent, EPService epService);

	public String instance(String agent, String rulebase, PrintWriter out);

}
