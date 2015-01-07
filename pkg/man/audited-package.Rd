\name{audited-package}
\alias{audited-package}
\alias{audited}
\docType{package}
\title{Automatic Tracing and Display of Changes to Row Count}
\description{
\pkg{audited} classifies a data.frame such that row deletions and
    additions are tracked.  A mechanism exists to give formal names to the row
    subsets added or deleted.  These names are used to populate a
    directed graph giving an account of all the transactions contributing to
    the state of the object.
}
\details{
\tabular{ll}{
Package: \tab audited\cr
Type: \tab Package\cr
Version: \tab 1.10\cr
Date: \tab 2014-09-24\cr
License: \tab GPL3\cr
}
	Audited data frames keep track of what happens to them, so later you can create
	a graph showing row deletions and additions.
	
	\code{\link{as.audited}} creates an \code{audited} data frame (which is also \code{keyed}).  You
	can supply a name (id) or accept the default (same as object name).  When you add or 
	delete rows using supported methods, a transaction will be stored in the audit table (bound
	to the object) indicating the number of changed rows and the resulting total.  
	If the data frame has a column listed in the vector \code{options('audit')} 
	(set this using \code{options(audit=)}), unique values of that column (first match) will be tracked 
	also. If \code{options('artifact')} is \code{TRUE} (default \code{NULL}) then dropped record sets 
        will be stored in a list as the \code{artifact} attribute of the audited data frame.
        (Alternatively, this can be a vector with any of \code{drop}, \code{add},
        \code{create}, \code{modify}, \code{transform} or \code{merge}:
        see \code{\link{artifact}} for details.)  \code{\link{as.xlsx}} writes artifacts 
        to a workbook.
	
}
\author{
Tim Bergsma

Maintainer: Tim Bergsma <timb@metrumrg.com>
}
\references{
\url{http://github.com/bergsmat/audited}, 
\url{http://metrumrg.googlecode.com}
}
\keyword{ package }
\seealso{
\code{\link{as.audited}}
\code{\link{plot.audited}}
\code{\link{as.xlsx.audited}}
\code{\link[metrumrg:metrumrg-package]{metrumrg}}
}
\examples{
options(audit='Subject')
options(artifact='drop')
rstudiogd()
pc <- data.frame(Theoph)
pc$Subject <- as.numeric(as.character(pc$Subject))
pc <- as.audited(pc,key=c('Subject','Time'))
ex <- pc[pc$Time == 0,,id='ex']
ex$EVID <- 1
pc$EVID <- 0
dat <- alias(id='dat', merge(pc, ex, all=TRUE))
dat <- dat[dat$Subject > 1,]
dat <- dat[dat$Wt > 70,,id='heavier subjects',od='lighter subjects']
audit(dat)
artifact(dat)

# default igraph aesthetics
plot(dat, list())

# unscaled audit aesthetics
plot(dat,scale=FALSE)

# default audit aesthetics
plot(dat)

# adjusting the label presentation
plot(dat, format='\%a sub\n\%l\n\%r row')

# adjusting vertex inflation
plot(dat,inflation=1.2)

# adjusting vertex proportion
plot(dat,proportion=1.2)

# progressively longer audit trails
dat2 <- dat[dat$Subject != 2,,od='subj 2']
dat3 <- dat2[dat2$Subject != 3,,od='subj 3']
dat4 <- dat3[dat3$Subject != 4,,od='subj 4']
dat6 <- dat4[dat4$Subject != 6,,od='subj 6']
dat8 <- dat6[dat6$Subject != 8,,od='subj 8']
dat9 <- dat8[dat8$Subject != 9,,od='subj 9']

# vertex and edge proportions nearly constant across scale
# alternatively, use scale=FALSE and change canvas (image) proportionately
plot(dat)
plot(dat2)
plot(dat3)
plot(dat4)
plot(dat6)
plot(dat8)
plot(dat9)

# a more neutral aesthetic
plot(
  dat3,
  vertex.shape='rectangle',
  vertex.color=NA, # or maybe 'white'
  create.vertex.color=NA,
  drop.vertex.color=NA,
  merge.vertex.color=NA,
  vertex.frame='black',
  edge.color='black',
  vertex.label.color='black',
  merge.edge.color='black',
  drop.edge.color='black'
)

\dontrun{
aud <- audit(dat)
write.audit(aud,'dat.audit')
aud <- read.audit('dat.audit')
as.xlsx(dat,'dat.xlsx')
}
}
