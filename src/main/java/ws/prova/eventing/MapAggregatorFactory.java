package ws.prova.eventing;

import java.io.Serializable;

public class MapAggregatorFactory implements ProvaStateObjectFactory {

	@Override
	public Serializable create() {
		return new MapAggregator();
	}

}
