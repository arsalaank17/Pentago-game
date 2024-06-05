package gamelogic.computer;

/**
 * The strategy factory interface
 * used to create a new type of strategy!
 * @author Kevin Schurman and Arsalaan Khan
 */
public interface StrategyFactory {

    /**
     * Creates a new NaiveStrategy!
     * @return A Naive Strategy object
     */
    Strategy makeNaiveStrategy();

    /**
     * Creates a new NaiveStrategy!
     * @return A smart strategy object
     */
    Strategy makeSmartStrategy();
}
