\name{write.audit}
\alias{write.audit}
\alias{read.audit}
\title{Write and Read Audits}
\description{Functions to write and read objects of class \code{audit}.}
\usage{
write.audit(x, file, quote = FALSE, row.names = FALSE, na = ".", ...)
read.audit(x, ...)
}
\arguments{
  \item{x}{an audit object, or a filename for read}
  \item{file}{passed to write.table}
  \item{quote}{passed to write.table}
  \item{row.names}{passed to write.table}
  \item{na}{passed to write.table}
  \item{\dots}{passed to write.table}
}
\value{for read, an object of class \code{audit}}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
	\item \code{\link{as.keyed}}
	\item \code{\link{as.audited}}
	\item \code{\link{as.keyed.audited}}
	\item \code{\link{as.igraph}}
	\item \code{\link{audit}}
	\item \code{\link{audited-package}}
	\item \code{\link{Ops.audited}}
	\item \code{\link{subset.audited}}
	\item \code{\link{melt.audited}}
	\item \code{\link{write.table}}
	}
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
