\name{as.audited}
\alias{as.audited}
\alias{as.audited.data.frame}
\alias{as.audited.keyed}
\alias{as.audited.audited}
\alias{as.audited.nm}
\alias{alias.audited}
\title{Create Audited Objects}
\description{
These methods coerce their arguments to class \code{audited}.  An audited
object keeps track of changes in row count caused by supported methods. The record of a 
change is called a transaction, and is stored in an audit table. The table is retrievable using
\code{\link{audit}} and can be plotted as a directed graph using \code{\link{plot.igraph}}.
}
\usage{
\method{as.audited}{data.frame}(x, key = character(0), id, ...)
\method{as.audited}{keyed}(x, key = match.fun('key')(x), id, ...)
\method{as.audited}{audited}(x, key = match.fun('key')(x), id, ...)
\method{as.audited}{nm}(x, key = match.fun('key')(x), id, ...)
\method{alias}{audited}(object, id, ...)
}
\arguments{
  \item{x}{object to be coerced}
  \item{key}{character; see \code{\link{as.keyed}}}
  \item{id}{optional name for this object for use in the audit table}
  \item{\dots}{ignored or passed}
  \item{object}{object to be aliased}
}
\details{
The argument \code{id} will be guessed from context if missing. 

\code{as.audited.audited} provides a chance to change the key or id of the object.  An additional record will be added if counts differ from most recent, 
even if no other changes are made. 

\code{alias.audited} updates the id not just on the object, but also in last result identifier
in the audit table. It supports the notion that the last transaction resulted in 
a new entity rather than merely a modification to an existing entity.

\code{as.audited.nm} promotes \code{('nm','keyed','data.frame')} to \code{('nm','audited','keyed','data.frame')}.
There is no going back: used on \code{('nm','audited','keyed','data.frame')} it gives 
simply \code{('audited','keyed','data.frame')}.
A passed key is respected. \code{id} is respected if passed; otherwise \code{id} is 
same as existing or is inferred from the argument.

}
\value{audited}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		  \item \code{\link{as.keyed}}
		  \item \code{\link{as.keyed.audited}}
		  \item \code{\link{as.igraph}}
		  \item \code{\link{audit}}
		  \item \code{\link{audited-package}}
		  \item \code{\link{Ops.audited}}
		  \item \code{\link{write.audit}}
		  \item \code{\link{subset.audited}}
		  \item \code{\link{melt.audited}}
		  \item \code{\link{cast,audited-method}}
		  \item \code{\link{cast,keyed-method}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
