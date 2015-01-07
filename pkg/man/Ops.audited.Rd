\name{Ops.audited}
\alias{Ops.audited}
\alias{^.audited}
\alias{!.audited}
\alias{|.audited}

\title{Binary and Unary Operations with Audited}
\description{

These are binary and unary operators like those for \code{keyed} data frames. 
\code{+} and \code{*} generate \code{add} transactions; \code{-} \code{&} and \code{/} 
generate \code{drop} transactions.  \code{!} inherits
the behavior of the subset operator, where \code{i} is \code{naKeys()} or \code{dupKeys()}.
\code{^} and \code{|} convert
their arguments to class \code{keyed}, perform the usual operation, and preserve attributes; they
are not expected to add or delete records, so the audit table is not updated.  The value
of these functions inherits the attributes of \code{e1} by default.  
}
\usage{
\method{Ops}{audited}(e1, e2)
\method{|}{audited}(e1, e2)
\method{^}{audited}(e1, e2)
\method{!}{audited}(e1)
}
\arguments{
  \item{e1}{left argument to binary operator, or only unary argument}
  \item{e2}{right argument to binary operator}
}
\value{audited}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		\item \code{\link{Ops.keyed}}
		\item \code{\link{as.keyed}}
		\item \code{\link{as.audited}}
		\item \code{\link{as.keyed.audited}}
		\item \code{\link{as.igraph}}
		\item \code{\link{audit}}
		\item \code{\link{audited-package}}
		\item \code{\link{write.audit}}
		\item \code{\link{subset.audited}}
		\item \code{\link{melt.audited}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
