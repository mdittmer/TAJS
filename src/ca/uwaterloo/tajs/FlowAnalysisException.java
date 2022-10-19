package ca.uwaterloo.tajs;

public class FlowAnalysisException extends RuntimeException {

  private static final long serialVersionUID = 1L;

  /**
   * Constructs a new exception.
   */
  public FlowAnalysisException() {
  }

  /**
   * Constructs a new exception.
   */
  public FlowAnalysisException(String msg) {
      super(msg);
  }

  /**
   * Constructs a new exception.
   */
  public FlowAnalysisException(Throwable t) {
      super(t);
  }

  /**
   * Constructs a new exception.
   */
  public FlowAnalysisException(String msg, Throwable t) {
      super(msg, t);
  }
}
