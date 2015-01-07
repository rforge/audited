\name{as.xlsx.artifact}
\alias{as.xlsx.audited}
\alias{as.xlsx.artifact}
\alias{as.xlsx}
\title{
  Convert Audit Artifacts to Excel Workbook
}
\description{
These functions save a collection of artifacts as an Excel 2007
workbook, optionally as a file, using package \pkg{xlsx}.
}
\usage{
\method{as.xlsx}{audited}(x, file = NULL, ...)
\method{as.xlsx}{artifact}(x, names, file = NULL, simplify = TRUE, gc = FALSE, ...)
}
\arguments{
  \item{x}{an audited object, or its artifact}
  \item{names}{names for the workbook sheets}
  \item{file}{a filename for the workbook}
  \item{simplify}{whether to drop artifacts with no rows}
  \item{gc}{whether to attempt garbage collection}
  \item{\dots}{passed to called functions}
}
\details{
All the hard work is done by the artifact method, but typically one
wants to call \code{as.xlsx} for an audited object so that names
can be supplied automatically.  In that case, they will be the vector
\code{arg.id} from the audit table.  Care is taken to make them unique.

If \code{simplify} is true, zero-row artifacts are ignored, and 
their names dropped if necessary.  (Names vector can have the length
either of the artifact list, or of the subset having 1 or more rows.)

If file is specified, the workbook is written to file and returned 
invisibly.  The workbook can be assigned in an environment for 
further manipulation.
}
\value{
a java pointer for a workbook, as for \code{createWorkbook()}; 
invisible if file is specified
}
\note{
For particularly large work sheets, you may need to run, e.g.,
\code{options(java.parameters = "-Xmx1000m")} 
(see \href{http://stackoverflow.com/questions/12625481/memoryerror-in-r-while-read-xlsx}{this})
or \code{options( java.parameters = "-Xmx4g" )} 
(see \href{http://www.bramschoenmakers.nl/en/node/726}{this}) 
before the first call to \code{as.xlsx}.  Also, you could pass \code{gc = TRUE}
in the call, possibly with performance and memory tradeoffs.
}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
  \itemize{
	  \item \code{\link{audit}}
    \item \code{\link{artifact}}
  }
}
\examples{
\donttest{example(audited)}
}
\keyword{manip}
