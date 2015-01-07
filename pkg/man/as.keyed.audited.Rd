\name{as.keyed.audited}
\alias{as.keyed.audited}
\alias{as.nm.audited}
\alias{as.digest.audited}
\alias{digest.audited}
\alias{combinations.audited}
\title{Coerce Audited to Related Class}
\description{

\code{as.keyed.audited} demotes \code{audited} to just \code{keyed}.  
\code{as.nm.audited} executes
\code{as.nm.keyed}, preserving \code{audited} class attributes. \code{digest} 
and \code{as.digest} call the \code{keyed} method,
preserving class attributes. The \code{combinations} method demotes to \code{keyed}
and calls the next method.
}
\usage{
\method{as.keyed}{audited}(x, key = match.fun('key')(x), ...)
\method{as.nm}{audited}(x, key = match.fun('key')(x), id, ...)
\method{as.digest}{audited}(x, ...)
\method{digest}{audited}(x, ...)
\method{combinations}{audited}(x, ...)
}
\arguments{
  \item{x}{object to be coerced}
  \item{key}{optional replacement key, see \code{\link{as.keyed}}}
  \item{id}{optional replacement id, see \code{\link{as.audited}}}
  \item{\dots}{passed to other methods or ignored}
}
\value{as.keyed and combinations: keyed; as.digest (digest): digest; as.nm: nm}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		\item \code{\link{as.keyed}}
		\item \code{\link{as.digest}}
		\item \code{\link{as.nm}}
		\item \code{\link{as.audited}}
		\item \code{\link{as.igraph}}
		\item \code{\link{audit}}
		\item \code{\link{audited-package}}
		\item \code{\link{Ops.audited}}
		\item \code{\link{write.audit}}
		\item \code{\link{subset.audited}}
		\item \code{\link{melt.audited}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
