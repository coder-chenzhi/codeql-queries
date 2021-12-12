/**
 * @kind path-problem
 * @description https://lgtm.com/query/3093844423637150268/
 * @author https://twitter.com/pwntester
 */
import java
import DataFlow::PathGraph
import semmle.code.java.dataflow.FlowSources


class LoggingCall extends MethodAccess {
  LoggingCall() {
    exists(RefType t, Method m |
      //t.hasQualifiedName("org.apache.log4j", "Category") or // Log4j 1
      t.hasQualifiedName("org.apache.logging.log4j", ["Logger", "LogBuilder"])
    |
      (
        m.getDeclaringType().getASourceSupertype*() = t or
        m.getDeclaringType().extendsOrImplements*(t)
      ) and
      m.getReturnType() instanceof VoidType and
      this = m.getAReference()
    )
  }

  /** Returns an argument which would be logged by this call. */
  Argument getALogArgument() { result = this.getArgument(_) }
}

private class LogInjectionConfiguration extends TaintTracking::Configuration {
  LogInjectionConfiguration() { this = "Log Injection" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) {
    sink.asExpr() = any(LoggingCall c).getALogArgument()
  }

}

from LogInjectionConfiguration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "$@ flows to log entry.", source.getNode(),
  "User-provided value"
