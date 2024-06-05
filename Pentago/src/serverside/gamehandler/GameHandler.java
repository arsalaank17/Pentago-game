package serverside.gamehandler;

import gamelogic.game.Game;
import serverside.clienthandler.ClientHandler;

import java.util.Map;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The game handler responsible for
 * handling the messages sent by the
 * client and sending messages to the client
 * when in a game of Pentago. Whenever a client
 * gets in a game, a new GameHandler
 * object is created for the client.
 * Before the game has started and after
 * the game has ended the ClientHandler handles
 * the client's messages.
 * @author Kevin Schurman and Arsalaan Khan.
 */
public interface GameHandler {
    /**
     * This method is used to add a clientHandler
     * to the waiting queue of a game.
     *
     * @param c the ClientHandler object to be added
     *          to the queue
     */
    void addQueue(ClientHandler c);

    /**
     * This method is used to access the ReentrantLock
     * used by this class to ensure thread-safety.
     *
     * @return the ReentrantLock used by this class.
     */
    ReentrantLock getLock();

    /**
     * This method is used to access the toQueue
     * condition used by this class which indicates
     * if a client is in a queue.
     *
     * @return toQueue which is the condition to indicate
     * if a client is in a Queue.
     */
    Condition getToQueue();

    /**
     * This method is used to access the toWaitAgain
     * condition used by this class which indicates
     * to the client when they should wait until making
     * a queuing request again.
     * @return toWaitAgain which is the condition to indicate
     * if a client is still waiting to be queued
     */
    Condition getToWaitAgain();

    /**
     * This method is used to access the getToPlay
     * condition used by this class which indicates
     * if 2 clients are in a queue and are ready to play.
     *
     * @return toPlay which is a condition that
     * indicates if 2 clients are waiting in the queue
     * to play a game.
     */
    Condition getToPlay();

    /**
     * This method is used to access the boardSignal
     * condition used by different classes which indicates
     * if the game has made a signal or done a specific task.
     * @return boardSignal which is the condition to indicate
     * if a game has made a signal
     */
    Condition getBoardSignal();

    /**
     * This method is used to access the condition
     * toDone which indicates if the client has just
     * finished a game.
     *
     * @return toDone which is a condition indicating
     * if the client has just finished a game.
     */
    Condition getToDone();

    /**
     * This method is used to remove the client from a game.
     * @param game - The game the client must be removed from
     */
    void removeInGame(Game game);

    Map<String, Integer> getScore();
}