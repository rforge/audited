\name{cast-methods}
\docType{methods}
\alias{cast,audited-method}
\title{ Methods for Function \code{cast} in Package \pkg{reshape} }
\description{
 Methods for function \code{cast} in package \pkg{reshape}.  \pkg{metrumrg} converts 
 \code{reshape::cast} to the default method for an S4 generic; it also promotes its own 
 S3 class \code{keyed} to an S4 class, and defines a \code{cast} method for it.
 Provided here is the analogous cast method for class \code{audited}.
}
\section{Methods}{
\describe{

\item{\code{signature(data = "audited")}}{
The method for \code{audited} is mostly a wrapper for \code{\link{cast,keyed-method}} that
maintains attributes.  It adds a `transform' transaction to the audit table.

}
}}
\keyword{methods}
\keyword{ manip }
