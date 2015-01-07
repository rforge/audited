\name{subset.audited}
\alias{subset.audited}
\alias{[.audited}
\alias{unique.audited}
\alias{head.audited}
\alias{tail.audited}
\alias{rbind.audited}
\title{Drop Methods for Class Audited}
\description{These methods alter the audited object and return it with an updated 
transaction table.  They generate \code{drop} transactions.}
\usage{
\method{[}{audited}(x, i, j, drop, id, od)
\method{subset}{audited}(x, subset, select, drop = FALSE, id, od = "! subset", ...)
\method{unique}{audited}(x, incomparables = FALSE, fromLast = FALSE, id, od = "! unique", ...)
\method{head}{audited}(x, n = 6L, ..., id, od = "! head")
\method{tail}{audited}(x, n = 6L, ..., id, od = "! tail")
\method{rbind}{audited}(..., deparse.level = 1)
}
\arguments{
  \item{id}{character (scalar); see details}
  \item{od}{character (scalar); see details}
  \item{x}{audited}
  \item{i}{passed to subset operator}
  \item{j}{passed to subset operator}
  \item{drop}{passed to other functions}
  \item{subset}{passed to subset.data.frame}
  \item{select}{passed to subset.data.frame}
  \item{\dots}{passed to other functions}
  \item{incomparables}{passed to unique}
  \item{fromLast}{passed to unique}
  \item{n}{passed to head or tail}
  \item{deparse.level}{as for rbind.data.frame}
}
\details{

The most important arguments here are \code{id} and \code{od}.  All the others
are passed through to related functions.

\code{id} and \code{od} will always have informative defaults.  However, you will often
want to supply customized values.  \code{id} is a label for the set of rows that is returned.
\code{od} is a label for the set of rows that is dropped; it will be used for plotting.

When supplying \code{id} or \code{od}, remember to maintain the proper number of dimensions.
For example, 

\code{Theoph[ Theoph$WT > 70, , id = 'heavier', od = 'lighter' ]} not 

\code{Theoph[ Theoph$WT > 70,   id = 'heavier', od = 'lighter' ]}

The subset operator, called by all the other functions listed above, deserves 
special consideration.  Argument \code{i} controls the rows that are returned. 
For a \code{data.frame}, \code{i} may be negative, positive, zero, logical, character, 
and NA, with varying effects. In particular, use of repeated 
positive creates duplicates of rows, while use of NA, numeric greater than
\code{nrow(x)}, or character not in \code{row.names(x)} creates NA rows.  \code{[.audited}
rejects indices that create NA rows. It allows duplication of rows, but it is an 
error to both add and drop rows simultaneously.
For example, \code{x[c(2,2),]} should fail, because record 1 (probably others)
is being dropped while a copy of record 2 is being added.
}
\value{audited}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		\item \code{\link{as.keyed}}
		\item \code{\link{as.audited}}
		\item \code{\link{as.keyed.audited}}
		\item \code{\link{as.igraph}}
		\item \code{\link{audit}}
		\item \code{\link{artifact}}
		\item \code{\link{audited-package}}
		\item \code{\link{Ops.audited}}
		\item \code{\link{melt.audited}}
		\item \code{\link{write.audit}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
