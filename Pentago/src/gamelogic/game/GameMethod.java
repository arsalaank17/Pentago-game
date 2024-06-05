package gamelogic.game;

import commands.ServerCommands;
import gamelogic.board.Board;
import gamelogic.board.BoardMethod;
import gamelogic.player.Mark;
import gamelogic.player.NetworkPlayer;
import gamelogic.player.Player;
import serverside.clienthandler.ClientHandler;
import serverside.gamehandler.GameHandler;

import java.io.PrintWriter;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Class for maintaining the Pentago game.
 * Module 2 Project 2022 University of Twente
 * @author Kevin Schurman and Arsalaan Khan
 */
public class GameMethod implements Game, Runnable {
    private static final int NUM_PLAYERS = 2;
    private final Board board;
    private final Player[] players;
    private PrintWriter pw;
    private ReentrantLock lock;
    private Condition signalBoard;
    private Object[] object;
    private int current;
    private int moves;

    /*@ private invariant board != null;
        private invariant players.length == NUM_PLAYERS;
        private invariant (\forall int i; (i >= 0 && i < NUM_PLAYERS); players[i] != null);
    */

    /**
     * Creates a GameMethod Object.
     * @param p1 player 1
     * @param p2 player 2
     */
    //@ requires p1 != null && p2 != null;
    public GameMethod(Player p1, Player p2) {
        board = new BoardMethod();
        players = new Player[NUM_PLAYERS];
        players[0] = p1;
        players[1] = p2;
        current = 0;
        moves = 0;
    }

    /**
     * Creates a GameMethod Object with a PrintWriter.
     * @param p1 player 1
     * @param p2 player 2
     * @param pw send out print writer data
     */
    //@ requires p1 != null && p2 != null && pw != null;
    public GameMethod(Player p1, Player p2, PrintWriter pw) {
        this(p1, p2);
        this.pw = pw;
    }

    /**
     * Creates a GameMethod Object with a couple of objects.
     * @param p1 player 1
     * @param p2 player 2
     * @param lock locks the board to do the signal
     * @param signalBoard tells the user whether to signal the board or not
     * @param object miscellaneous for gameHandler specifics
     */
    //@ requires p1 != null && p2 != null && lock != null && signalBoard != null && object != null;
    public GameMethod(Player p1, Player p2, ReentrantLock lock, Condition signalBoard,
                      Object... object) {
        this(p1, p2);
        this.lock = lock;
        this.signalBoard = signalBoard;
        this.object = object;
    }


    /**
     * Starts the Pentago game.
     * Continues until either the board has a winner or the board is full
     */
    @Override
    public void startGame() {
        current = 0;
        board.reset();
        boolean disconnected = false;
        while (!board.gameOver()) {
            Player player = players[current];
            boolean valid = false;
            do {
                if (player instanceof NetworkPlayer) {
                    Integer[] playerInput = ((NetworkPlayer) player).getInData();
                    if (playerInput == null) {
                        disconnected = true;
                        break;
                    }
                    if (board.isField(playerInput[0])
                            && board.isEmptyField(playerInput[0])
                            && board.isRotation(playerInput[1])) {
                        board.setField(playerInput[0], player.getMark());
                        if (board.gameOver()) {
                            break;
                        }
                        board.rotatePart(playerInput[1]);
                        for (Player p : players) {
                            if (p instanceof NetworkPlayer
                                    && ((NetworkPlayer) p).getOut() != null) {
                                ((NetworkPlayer) p).getOut().println(
                                        ServerCommands.sMOVE(playerInput[0], playerInput[1]));
                            }
                        }
                        valid = true;
                    } else {
                        if (((NetworkPlayer) player).getOut() != null) {
                            ((NetworkPlayer) player).getOut().println(
                                    ServerCommands.sERROR("Wrong move buddy"));
                            try {
                                Thread.sleep(10);
                            } catch (InterruptedException e) {
                                e.printStackTrace();
                            }
                        }
                    }
                } else {
                    int move = player.makeMove(board.deepCopy());
                    int rotation = player.makeRotate(board.deepCopy());
                    if (board.isField(move)
                            && board.isEmptyField(move)
                            && board.isRotation(rotation)) {
                        board.setField(move, player.getMark());
                        if (board.gameOver()) {
                            break;
                        }
                        board.rotatePart(rotation);
                        valid = true;
                    }
                }
            } while (!valid);
            if (board.gameOver() || disconnected) {
                break;
            }
            current = 1 - current;
            moves++;
            if (pw != null) {
                pw.println(board);
            }
            if (lock != null && signalBoard != null) {
                lock.lock();
                signalBoard.signalAll();
                lock.unlock();
            }
        }
        String status = null, winner = null;
        if (board.hasWinner()) {
            status = "VICTORY";
            winner = (board.isWinner(players[0].getMark()) ? players[0] : players[1]).getName();
        } else if (board.gameOver()) {
            status = "DRAW";
        } else if (disconnected) {
            status = "DISCONNECT";
            winner = players[1 - current].getName();
        }
        for (Player p : players) {
            if (p instanceof NetworkPlayer && ((NetworkPlayer) p).getOut() != null) {
                ((NetworkPlayer) p).getOut().println((winner != null)
                        ? ServerCommands.sGAMEOVER(status, winner)
                        : ServerCommands.sGAMEOVER(status));
            }
        }

        if (object != null && object.length > 0) {
            GameHandler gh = (GameHandler) object[0];
            ClientHandler[] ch = (ClientHandler[]) object[1];
            for (Player player : players) {
                if (board.isWinner(player.getMark())) {
                    if (gh.getScore().get(player.getName()) != null) {
                        int score = gh.getScore().get(player.getName()) + 100;
                        gh.getScore().remove(player.getName());
                        gh.getScore().put(player.getName(), score);
                    } else {
                        gh.getScore().put(player.getName(), 100);
                    }
                }
            }
            gh.getLock().lock();
            ch[0].setInGame(false);
            ch[1].setInGame(false);
            gh.getToDone().signalAll();
            gh.removeInGame(this);
            gh.getLock().unlock();
        }

        if (lock != null && signalBoard != null) {
            lock.lock();
            signalBoard.signalAll();
            lock.unlock();
        }
    }

    /**
     * Prints the game situation.
     * @return String of the current updated board
     */
    //@ requires getBoard() != null;
    /*@ pure */
    @Override
    public String update() {
        return "Current situation:\n" + board;
    }

    /**
     * Prints the result of the last game.
     * @return String of the result of the board
     */
    //@ requires getBoard().hasWinner() || getBoard().gameOver();
    /*@ pure */
    @Override
    public String result() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMark()) ? players[0] : players[1];
            return "Player " + winner.getName() + " " + (winner.getMark() == Mark.WHITE
                    ? (char) 27 + "[30;47;1m("
                    : (char) 27 + "[37;40;1m(")
                        + winner.getMark() + ")" + (char) 27 + "[0m" + " has won!\n";
        } else if (board.gameOver()) {
            return "Draw. There is no winner!\n";
        } else {
            return "Board has no winner and has not been Gamed Over.";
        }
    }

    /**
     * This method is used to return the Pentago Board object
     * @return Board of the current board
     */
    //@ requires true;
    /*@ pure */
    @Override
    public Board getBoard() {
        return board;
    }

    /**
     * This method is used to return the players in the Pentago game
     * @return Player[] of the player arrays
     */
    //@ requires true;
    /*@ pure */
    @Override
    public Player[] getPlayers() {
        return players;
    }

    /**
     * This method is used to return the Player object whose turn it is
     * in the Pentago game
     * @return Player of the currently playing player
     */
    //@ requires true;
    /*@ pure */
    @Override
    public Player getCurrent() {
        return players[current];
    }

    /**
     * This method is used to return the amount of moves made
     * in the Pentago game
     * @return int of the amount of moves made in the game
     */
    //@ requires true;
    /*@ pure */
    @Override
    public int getMoves() {
        return moves;
    }

    @Override
    public void run() {
        startGame();
    }
}