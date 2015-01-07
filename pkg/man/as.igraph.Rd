\name{as.igraph}
\alias{as.igraph.audit}
\alias{as.igraph.audited}
\alias{plot.audited}
\alias{format.state}
\alias{auditAttrs}
\alias{auditAttrs.audited}
\alias{auditAttrs.audit}
\alias{auditAttrs.default}
\alias{maxchar}
\alias{maxchar.audit}
\alias{deconvolute}
\alias{modulate}
\alias{modulation}
\alias{modulationRStudioGD}
\alias{rstudiogd}
\alias{modulation.default}
\alias{distend}
\alias{project}
\title{Visualize an Audit Transaction Table}
\description{

Objects of class \code{audited} have embedded transaction tables 
that can be retrieved as an object of class \code{audit} using \code{audit(x)}.
The \code{plot} method for class \code{audited} extracts the \code{audit} table,
converts it to \code{igraph} using \code{as.igraph}, and plots it with the plot method
for class \code{igraph}. For fine control of plotting characteristics, you can load \pkg{igraph}
and reproduce the sequence manually.
}
\usage{
\method{plot}{audited}(x,attrs=auditAttrs(x,...),...)
auditAttrs(x=NULL,...)
\method{auditAttrs}{audited}(x,...)
\method{auditAttrs}{audit}(
	x,
	inflation = 1,
	proportion = 1,
	canvas.nominal = 7,
	dimension.nominal = 4,
	chars.nominal = 6,
	vertex.nominal = 30 * inflation,
	vertex.aspect = 1.618,
	canvas = min(dev.size()),
	chars = max(chars.nominal,maxchar(x)),
	dimension = max(nrow(x),2),
	dimension.scale = dimension.nominal / dimension,
	deconvolution = deconvolute(canvas,canvas.nominal),
	modulation = modulate(dev.name()),
	projection = project(canvas.nominal)/project(canvas),
	distention = distend(max(dimension,2),  1.5 / dimension.nominal),
	canvas.scale = canvas / canvas.nominal,
	chars.scale = chars.nominal / chars,
	edge.scale = dimension.scale * canvas.scale * projection,
	vertex.scale =       dimension.scale * deconvolution 
	* distention * projection * proportion * modulation,
	vertex.label.scale = dimension.scale * canvas.scale  
	* distention * projection * proportion * chars.scale,
	vertex.size = vertex.nominal * vertex.scale ^ scale,
	vertex.size2 = vertex.size / vertex.aspect ^ scale,
	vertex.label.cex = vertex.label.scale ^ scale,
	edge.width =      edge.scale ^ scale, 
	edge.arrow.size = edge.scale ^ scale,
	edge.arrow.width =  1,
	scale=TRUE,
	rescale=!scale,
	...
)
\method{auditAttrs}{default}(
	x,
	color = TRUE,
	vertex.shape = 'circle',
	vertex.size = 15,
	vertex.size2 = vertex.size,
	vertex.color =         if (color) 'lightgreen' else NA,
	vertex.frame.color =   if (color) NA           else 'black',
	vertex.label.color =   if (color) 'darkblue'   else 'black',
	vertex.label.cex = 1,
	vertex.label.family = 'mono',
	edge.color =           if (color) 'darkgreen'  else 'black',
	edge.width = 1,
	edge.arrow.size = 1,
	edge.arrow.width = 1,
	edge.label.color = vertex.label.color,
	edge.label.cex = vertex.label.cex,
	create.vertex.color =  if (color) 'gold'       else NA,
	drop.vertex.color =    if (color) 'pink'       else NA,
	drop.edge.color =      if (color) 'red'        else 'black',
	drop.edge.label =      if (color) NA           else 'drop',
	add.vertex.color =     if (color) 'lightblue'  else NA,
	add.edge.color =       if (color) 'blue'       else 'black',
	add.edge.label =       if (color) NA           else 'add',
	merge.vertex.color =   if (color) 'orchid'     else NA,
	merge.edge.color =     if (color) 'orchid4'    else 'black',
	merge.edge.label =     if (color) NA           else 'merge',
	transform.edge.label = if (color) NA           else '',
	modify.edge.label =    if (color) NA           else '',
	rescale = FALSE,
	...
)
\method{format}{state}(x,format='\n\%l\n\%r',...)
}
\arguments{
  \item{x}{object of method dispatch}
  \item{inflation}{adjust vertex size relative to text size; default 1}
  \item{proportion}{adjust vertex and text size relative to vertex spacing; default 1}
  \item{format}{a format string for text of vertices; default: label over record count}
  \item{color}{logical: whether to use colorful defaults}
  \item{vertex.shape}{vertex shape; circle (default) and rectangle are well-supported}
  \item{vertex.color}{fill color}
  \item{vertex.frame.color}{frame color (default NA gives none)}
  \item{vertex.label.color}{vertex label color}
  \item{vertex.label.cex}{vertex label character expansion}
  \item{vertex.label.family}{vertex label family; default mono}
  \item{edge.label.color}{edge label default color}
  \item{edge.label.cex}{edge label cex}
  \item{edge.color}{default edge color}
  \item{create.vertex.color}{edge color for create events} 
  \item{drop.vertex.color}{vertex color for drop events}  
  \item{drop.edge.color}{edge color for drop events}  
  \item{drop.edge.label}{edge label for drop events}
  \item{add.vertex.color}{vertex color for add events}  
  \item{add.edge.color}{edge color for add events}  
  \item{add.edge.label}{edge label for add events}
  \item{merge.vertex.color}{vertex color for merge events}  
  \item{merge.edge.color}{edge color for merge events}  
  \item{merge.edge.label}{edge label for merge events (see details)}
  \item{transform.edge.label}{edge label for transform events (see details)}
  \item{modify.edge.label}{edge label for modify events}
  \item{canvas.nominal}{reference canvas size}
  \item{dimension.nominal}{reference graph dimension}
  \item{chars.nominal}{reference label width in monospaced characters}
  \item{vertex.nominal}{reference vertex size}
  \item{vertex.aspect}{ratio of vertex size and vertex size2}
  \item{canvas}{effective canvas size}
  \item{chars}{effective label width in monospaced characters}
  \item{dimension}{effective graph dimension}
  \item{dimension.scale}{dimension scale factor}
  \item{deconvolution}{size-specific adjustment of vertex size (for strict proportionality)}
  \item{modulation}{device-specific adjustment of vertex size}
  \item{distention}{dimension-specific adjustment of vertex size}
  \item{projection}{canvas-specific adjustment of vertex size}
  \item{canvas.scale}{canvas scale factor}
  \item{chars.scale}{label width scale factor}
  \item{edge.scale}{edge scale factor}
  \item{vertex.scale}{vertex scale factor}
  \item{vertex.label.scale}{vertex label scale factor}
  \item{vertex.size}{vertex size}
  \item{vertex.size2}{vertex secondary size}
  \item{edge.width}{edge width}
  \item{edge.arrow.size}{edge arrow size}
  \item{edge.arrow.width}{edge arrow width}
  \item{scale}{logical: whether to apply scale factors (default TRUE)}
  \item{rescale}{logical: whether to use igraph-rescaling (default FALSE) }
  \item{attrs}{list; see details}
  \item{\dots}{passed to called functions}
  
  
}
\details{
An audited data frame \code{x} has a default visualization by means of \code{plot(x)}.  
Labels and record counts are plotted in circles with colors that represent transaction types;
these are joined by arrows that represent transaction sequence.  The option
\code{color = FALSE} gives a black-and-white aesthetic with transaction types as
edge labels.

Default sizes are chosen to maintain a constant aesthetic regardless of transaction count, 
label length, device, and (particularly) device size. Some effort is made to contain
the label text within the vertex, and to make the vertex size about .35 of the inter-vertex
distance.  These can be adjusted with arguments \code{inflation} and \code{proportion}.

The \code{format} argument controls how labels are displayed.  It supports tokens 
\%l, \%r, and \%a, representing the vertex label (id), the integer number of 
records, and the integer number of aggregates, respectively. By default, record 
number is printed under the label, with a blank line above (which centers the 
label portion in the vertex).

You should not usually need to be concerned with arguments other than \code{inflation},
\code{proportion}, \code{format}, and perhaps \code{shape}.  Since the plot is 
implemented with the directed graph from \pkg{igraph}, additional arguments can 
be specified in the form \code{vertex.parameter} or \code{edge.parameter} ('parameter' not literal).  
See \code{\link{igraph.plotting}} for a full list. You can generate transaction-specific
parameters by prepending \code{create}, \code{add}, \code{drop}, \code{modify}, 
\code{transform}, \code{merge}; for example \code{merge.vertex.parameter}.

Set any parameter to NULL to defeat the defaults given above.  Set \code{attrs} to
\code{list()} to defeat all defaults, giving igraph-native aesthetics.

Although most methods can be visualized as binary, several are inherently unary,
such as \code{as.audited}, \code{aggregate}, \code{melt}, and \code{cast}. These
have an operation type of \code{modify} or \code{transform}, and they store a hint
about the actual method name in \code{arg.id}.  The hint resurfaces as edge label
if the corresponding argument (\code{modify.edge.label, transform.edge.label}) is
an empty string (default when \code{color = FALSE}). Pass \code{NULL} or \code{NA} 
to suppress edge labels.

}
\value{\code{plot}: an invisible list of the effective (supplied) parameters; \code{auditAttrs}: a list}
\note{
The algorithms here try to emulate the aesthetics of a four-record transaction table 
plotted with 6-character labels on a 7-inch pdf device.  You are welcome
to experiment with \code{dimension.nominal}, \code{chars.nominal}, \code{canvas.nominal},
and \code{vertex.nominal}.

Arrows and vertex frames (when printed) do not scale well for device sizes much less than 7 inches. 

You can supply a device-specific adjustment by defining a method \code{modulation.device} ('device' not literal).  
The function \code{rstudiogd()} is an experimental convenience that defines \code{modulation.RStudioGD} for 
rapid prototyping that transfers well to pdf.

Dots arguments to \code{plot.audited} are passed to \code{as.igraph} but not
to \code{plot} because \code{plot.igraph} does not support unrecognized arguments. 

For x with class path 
\code{('nm','audited','keyed','data.frame')}, consider \code{plot(as.audited(x))} which
will demote to audited, and so give the audited rather than nm plotting behavior.
}
\references{\url{http://metrumrg.googlecode.com},
\url{http://en.wikipedia.org/wiki/Golden_rectangle} (\code{vertex.aspect})}
\author{Tim Bergsma}
\seealso{
	\itemize{
  	\item \code{\link{plot.igraph}}
  	\item \code{\link{igraph.plotting}}
	\item \code{\link{as.keyed}}
	\item \code{\link{as.audited}}
	\item \code{\link{as.keyed.audited}}
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
