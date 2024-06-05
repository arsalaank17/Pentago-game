package gamelogic.computer;

/**
 * The strategy factory class used to create
 * a new type of strategy! Implements the
 * StrategyFactory interface!
 * @author Kevin Schurman and Arsalaan Khan
 */

public class StrategyFactoryMethod implements StrategyFactory {

    /**
     * Creates a new NaiveStrategy!
     * @return A Naive Strategy object
     */
    @Override
    public Strategy makeNaiveStrategy() {
        return new NaiveStrategy();
    }

    /**
     * Creates a new NaiveStrategy!
     * @return A smart strategy object
     */
    @Override
    public Strategy makeSmartStrategy() {
        return new SmartStrategy();
    }
}
