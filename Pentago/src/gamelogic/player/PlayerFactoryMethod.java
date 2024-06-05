package gamelogic.player;

import gamelogic.computer.Strategy;

import java.io.PipedReader;
import java.io.PrintWriter;
import java.io.Reader;
/**
 * The class for the PlayerFactoryMethod!
 * PlayerFactoryMethod will be used to create new
 * types of players in the pentago game.
 * The types of players include computer player,
 * human player and the network player. Implements
 * the interface PlayerFactory.
 * @author Kevin Schurman and Arsalaan Khan
 */
public class PlayerFactoryMethod implements PlayerFactory {

    /**
     * The method used to create a new computer
     * player object!
     * @param strategy - The strategy of the computer
     *                 player. Could be Naive or Smart
     * @param mark - The mark of the computer player. Could
     *             be Black or White
     * @return a Player object which is going to be a computer
     * player with the passed parameters
     */
    @Override
    public Player makeComputerPlayer(Strategy strategy, Mark mark) {
        return new ComputerPlayer(strategy, mark);
    }

    /**
     * The method used to make a new human player
     * object!
     * @param name - A string containing the
     *             name of the humanPlayer.
     * @param reader - The reader used to read
     *               any incoming data.
     * @param mark - The mark of the human player.
     *             Could be black or White.
     * @return a Player object which is going to be
     * a human player with the passed parameters.
     */
    @Override
    public Player makeHumanPlayer(String name, Reader reader, Mark mark) {
        return new HumanPlayer(name, reader, mark);
    }

    /**
     * The method used to make a new human player
     * object!
     * @param name - A string containing the
     *             name of the humanPlayer.
     * @param reader - The reader used to read
     *               any incoming data.
     * @param mark - The mark of the human player.
     *             Could be black or White.
     * @param pw - The printWriter so the player can
     *           view what is going on.
     * @return a Player object which is going to be
     * a human player with the passed parameters.
     */
    @Override
    public Player makeHumanPlayer(String name, Reader reader, Mark mark, PrintWriter pw) {
        return new HumanPlayer(name, reader, mark, pw);
    }

    /**
     * The method used to make a new Network player
     * object!
     * @param name - The name of the network player.
     * @param in - The PipedReader used to read the incoming
     *           data from the server.
     * @param mark - The mark of the network player. Could
     *             be black or white.
     * @param out - The printWriter used to send data to the server.
     * @return - a Player object which is going to be
     * a NetworkPlayer with the passed parameters.
     */
    @Override
    public Player makeNetworkPlayer(String name, PipedReader in, Mark mark, PrintWriter... out) {
        return new NetworkPlayer(name, in, mark, out);
    }
}
