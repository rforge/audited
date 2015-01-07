\name{audited-class}
\Rdversion{1.2}
\docType{class}
\alias{audited-class}

\title{Class \code{"audited"}}
\description{
This class is a \code{keyed} data frame with an audit table of transactions and 
an \code{id} attribute.
The class is implemented as S3, and is promoted to S4 to take advantage of S4 generic 
mechanisms.
}
\section{Objects from the Class}{A virtual Class: No objects may be created from it.}
\section{Slots}{
  \describe{
    \item{\code{.Data}:}{Object of class \code{"list"}}
    \item{\code{names}:}{Object of class \code{"character"}}
    \item{\code{row.names}:}{Object of class \code{"data.frameRowLabels"} }
    \item{\code{.S3Class}:}{Object of class \code{"character"} }
  }
}
\section{Extends}{
Class \code{"\linkS4class{keyed}"}, directly.
Class \code{"\linkS4class{data.frame}"}, by class "keyed", distance 1.
Class \code{"\linkS4class{list}"}, by class "data.frame", distance 2.
Class \code{"\linkS4class{oldClass}"}, by class "data.frame", distance 2.
Class \code{"\linkS4class{vector}"}, by class "data.frame", distance 3.
}
\references{\url{http://metrumrg.googlecode.com}}
\author{Tim Bergsma}
\seealso{
  \itemize{
		\item \code{\link{as.audited}}
		\item \code{\link{keyed-class}}
	}
}
\examples{
showClass("keyed")
}
\keyword{classes}
