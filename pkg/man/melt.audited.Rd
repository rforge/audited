\name{melt.audited}
\alias{aggregate.audited}
\alias{melt.audited}
\alias{merge.audited}
\title{Transform Methods for Class Audited}
\description{These methods alter the audited object and return it with an updated 
transaction table.  They are based on the corresponding methods
for class keyed, and generate `transform' transactions (aggregate, melt) or 
`merge` transactions (merge).}
\usage{
\method{aggregate}{audited}(
	x, 
	by = x[, setdiff(key(x), across), 
	drop = FALSE], 
	FUN, 
	across = character(0), 
	...
)
\method{melt}{audited}(
	data, 
	id.vars = key(data), 
	measure.vars, 
	variable_name = "variable", 
	na.rm = FALSE, 
	...
)
\method{merge}{audited}(
	x, 
	y, 
	strict = TRUE, 
	...
)
}
\arguments{
  \item{x}{audited object}
  \item{\dots}{passed to other methods}
  \item{by}{passed to aggregate.keyed}
  \item{FUN}{passed to aggregate.keyed}
  \item{across}{passed to aggregate.keyed}
  \item{data}{passed to melt.keyed}
  \item{id.vars}{passed to melt.keyed}
  \item{measure.vars}{passed to melt.keyed}
  \item{variable_name}{passed to melt.keyed}
  \item{na.rm}{passed to melt.keyed}
  \item{y}{right element of a join}
  \item{strict}{prevent dropping records from x}
}
\value{audited}
\note{\code{merge} can drop or add records, or both.  It is an error if 
	\code{strict} is TRUE and any records in x have no representation
	(match on common columns) in the result.  I.e., merge cannot
	drop records without your expressed permission.  Beware that due
	to the rules for \code{base::merge}, record counts may not be 
	strictly additive when merging.
}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		\item \code{\link{cast,audited-method}}		
		\item \code{\link{as.keyed}}
		\item \code{\link{as.audited}}
		\item \code{\link{as.keyed.audited}}
		\item \code{\link{as.igraph}}
		\item \code{\link{audit}}
		\item \code{\link{audited-package}}
		\item \code{\link{Ops.audited}}
		\item \code{\link{subset.audited}}
		\item \code{\link{write.audit}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
