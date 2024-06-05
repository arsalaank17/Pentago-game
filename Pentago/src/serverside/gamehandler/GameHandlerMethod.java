package serverside.gamehandler;

import commands.ServerCommands;
import gamelogic.game.Game;
import gamelogic.game.GameMethod;
import gamelogic.player.Mark;
import gamelogic.player.NetworkPlayer;
import gamelogic.player.Player;
import serverside.clienthandler.ClientHandler;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
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
public class GameHandlerMethod implements GameHandler, Runnable {
    private final List<ClientHandler> queue = new ArrayList<>();
    private final Map<Game, Thread> inGame = new HashMap<>();
    private final Map<String, Integer> score = new HashMap<>();

    private final ReentrantLock lock = new ReentrantLock();
    private final Condition toQueue = lock.newCondition();
    private final Condition toWaitAgain = lock.newCondition();
    private final Condition toPlay = lock.newCondition();
    private final Condition boardSignal = lock.newCondition();
    private final Condition toDone = lock.newCondition();

    /**
     * This method is used to add a clientHandler
     * to the waiting queue of a game.
     * @param c the ClientHandler object to be added
     *          to the queue
     */
    @Override
    public void addQueue(ClientHandler c) {
        queue.add(c);
    }

    /**
     * This method is used to access the ReentrantLock
     * used by this class to ensure thread-safety.
     * @return the ReentrantLock used by this class.
     */
    @Override
    public ReentrantLock getLock() {
        return lock;
    }

    /**
     * This method is used to access the toQueue
     * condition used by this class which indicates
     * if a client is in a queue.
     * @return toQueue which is the condition to indicate
     * if a client is in a Queue.
     */
    @Override
    public Condition getToQueue() {
        return toQueue;
    }

    /**
     * This method is used to access the toWaitAgain
     * condition used by this class which indicates
     * to the client when they should wait until making
     * a queuing request again.
     * @return toWaitAgain which is the condition to indicate
     * if a client is still waiting to be queued
     */
    @Override
    public Condition getToWaitAgain() {
        return toWaitAgain;
    }

    /**
     * This method is used to access the getToPlay
     * condition used by this class which indicates
     * if 2 clients are in a queue and are ready to play.
     * @return toPlay which is a condition that
     * indicates if 2 clients are waiting in the queue
     * to play a game.
     */
    @Override
    public Condition getToPlay() {
        return toPlay;
    }

    /**
     * This method is used to access the boardSignal
     * condition used by different classes which indicates
     * if the game has made a signal or done a specific task.
     * @return boardSignal which is the condition to indicate
     * if a game has made a signal
     */
    public Condition getBoardSignal() {
        return boardSignal;
    }

    /**
     * This method is used to access the condition
     * toDone which indicates if the client has just
     * finished a game.
     * @return toDone which is a condition indicating
     * if the client has just finished a game.
     */
    @Override
    public Condition getToDone() {
        return toDone;
    }

    /**
     * This method is used to remove the client from a game.
     * @param game - The game the client must be removed from
     */
    @Override
    public void removeInGame(Game game) {
        inGame.remove(game);
    }

    /**
     * This method is used to get access to the map of the total
     * score of winners sets by every player who was currently playing.
     * @return score map of games
     */
    @Override
    public Map<String, Integer> getScore() {
        return score;
    }

    /**
     * Since this class is a runnable it
     * has a run method which is executed everytime
     * a new Thread of this class is started. This method
     * handles the messages sent by the client and sends
     * messages to the client accordingly. It also manipulates
     * various variables to ensure thread-safety and a smooth
     * gaming experience for the client while in game.
     */
    @Override
    public void run() {
        int number = 0;
        while (true) {
            try {
                lock.lock();
                toQueue.await();
                if (queue.size() > 1) {
                    ClientHandler[] ch = new ClientHandler[] {queue.get(0), queue.get(1)};
                    Player[] pl = new Player[2];
                    Mark[] mk = new Mark[]{Mark.WHITE, Mark.BLACK};
                    for (int i = 0; i < ch.length; i++) {
                        pl[i] = new NetworkPlayer(
                                ch[i].getUsername(), ch[i].getGameIn(), mk[i], ch[i].getOut());
                        ch[i].setInGame(true);
                        ch[i].sendToClient(ServerCommands.sNEWGAME(
                                ch[0].getUsername(), ch[1].getUsername()));
                        queue.remove(0);
                    }
                    Game game = new GameMethod(pl[0], pl[1], lock, boardSignal, this, ch);
                    inGame.put(game, new Thread((Runnable) game, "Game-Thread-" + number));
                    toPlay.signalAll();
                    inGame.get(game).start();
                }
                lock.unlock();
            } catch (InterruptedException e) {
                e.printStackTrace();
                break;
            }
        }
    }
}
