package ws.prova.eventing;

import java.io.Serializable;

public class AggregatorFactory implements ProvaStateObjectFactory {

	@Override
	public Serializable create() {
		return new Aggregator();
	}

}
