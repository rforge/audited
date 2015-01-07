\name{audit}
\alias{audit}
\alias{audit.audited}
\alias{audit<-}
\alias{audit<-.audited}
\alias{artifact}
\alias{artifact.audited}
\alias{artifact<-}
\alias{artifact<-.audited}
\alias{dev.name}

\title{Retrieve or Assign the Audit and Artifact Attributes}
\description{

Use \code{audit(x)} to retrieve the transaction table for an audited object. 

If possible, operations whose names appear in the vector \code{options('artifact')} 
store the changed records in the artifact list, which can be retrieved using \code{artifact(x)}.  
Length of the artifact list is always equal to number of records in the audit table, and elements 
correspond to audit records. However, artifacts will have zero rows by default.
For example if you specify \code{options(artifact='drop')} or \code{options(artifact=TRUE)}
then any dropped records are archived; \code{add} operations etc. generate header only.
Other possible character elements are \code{add}, \code{create}, \code{transform},
\code{merge}, and \code{modify}.
For \code{merge}, the artifact, if any, is simply \code{y}.

Normally one should not need to use the assignment forms.

}

\usage{
\method{audit}{audited}(x, ...)
\method{artifact}{audited}(x, ...)
audit(x) <- value
artifact(x) <- value
}
\arguments{
  \item{x}{an audited object}
  \item{\dots}{ignored}
  \item{value}{an audit object}
}
\value{for assignment: the audited object; for retrieval: the audit or artifact attribute}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
	\itemize{
		  \item \code{\link{as.keyed}}
		  \item \code{\link{as.audited}}
		  \item \code{\link{as.keyed.audited}}
		  \item \code{\link{as.igraph}}
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
