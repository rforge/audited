#library(igraph)
#library(metrumrg)
.as.state <- function(x, ...)UseMethod('.as.state')
.as.state.audited <- function(x,...){ # 
  agg <- .agg(x)
  rec <- .rec(x)
  res <- data.frame(stringsAsFactors=FALSE,id=.id(x),agg=agg,rec=rec)
  class(res) <- c('state',class(res))
  res
}
.as.event <- function(x,...)UseMethod('.as.event')
.as.event.character <- function(x,arg,res,...){
  stopifnot(x %in% c('add','drop','modify','create','transform','merge'), inherits(arg,'state'), inherits(res,'state'))
  names(arg) <- paste(sep='.','arg',names(arg))
  names(res) <- paste(sep='.','res',names(res))
  y <- data.frame(stringsAsFactors=FALSE,op=x,arg,res)
  class(y) <- c(x,'event', class(y))
  y
}
.as.state.event <- function(x,...,arg=TRUE){
  y <- if(arg) x[,2:4] else x[,5:7]
  names(y) <- c('id','agg','rec')
  class(y) <- c('state',class(y))
  y
}
.as.event.audit <- function(x,...){
  stopifnot(nrow(x) == 1 )
  class(x) <- c(x$op,'event','data.frame')
  x
}
.term <- function(x){
  terms <- options('audit')[[1]]
  terms <- terms %n% names(x)
  if(length(terms)==0)return(as.character(NA))
  term <- terms[[1]]
  term
}
.artifact <- function(x){
  a <- options('artifact')[[1]]
  if(length(a) == 1)if(is.logical(a))if(a==TRUE) a <- 'drop'
  length(a) && x %in% a
}
.agg <- function(x,...)UseMethod('.agg')
.agg.data.frame <- function(x,...){
  term <- .term(x)
  if(is.na(term))return(as.numeric(NA))
  length(unique(x[[term]]))
}
.rec <- function(x,...)UseMethod('.rec')
.rec.data.frame <- function(x,...)nrow(x)
as.audited <- function(x,...)UseMethod('as.audited')
as.audited.data.frame <- function(x, key=character(0), id, ...){
  if(missing(id)) id <- deparse(substitute(x))[[1]]
  x <- as.keyed(x,key=key,...)
  x <- as.audited(x,id=id,...)
  x
}
alias.audited <- function(object, id, ...){
  x <- object
  x <- as.audited(x, id = id, ...)
  id <- .id(x)
  aud <- audit(x)
  aud$res.id[nrow(aud)] <- id
  audit(x) <- aud
  x
}	
# This function deconstructs the audited class, to expose underlying methods.
as.keyed.audited <- function(x,key = match.fun('key')(x),...){
  .id(x) <- NULL
  audit(x) <- NULL
  artifact(x) <- NULL
  class(x) <- class(x) %-% 'audited'
  key(x) <- key
  x
}
# This should be the only function that implements the audited class.
as.audited.keyed <- function(x, key = match.fun('key')(x), id, ...){
  if(missing(id)) id <- deparse(substitute(x))[[1]]
  x <- as.keyed(x,key)
  class(x) <- union('audited' , class(x))
  id <- as.character(id)
  stopifnot(length(id) == 1)
  .id(x) <- id
  audit(x) <- .as.event('create',.as.state(x),.as.state(x))
  artifact(x) <- list(as.keyed(x)[0,,drop=FALSE])
  x
}
#         nm keyed data.frame -> nm audited keyed data.frame
# nm audited keyed data.frame -> audited keyed data.frame
as.audited.nm <- function(x, key = match.fun('key')(x), id, ...){
  demotion <- inherits(x,'audited')
  if(missing(id)) id <- if(demotion) .id(x) else deparse(substitute(x))[[1]]
  class(x) <-  class(x) %-% 'nm'
  x <- as.audited(x, key=key, id=id,...)
  if(!demotion) class(x) <- 'nm' %+% class(x)
  x
}
as.audited.audited <- function(x, key = match.fun('key')(x), id, ...){
  if (!missing(key) && !(all(key %in% names(x))))warning('key columns not all in names(x)')
  if (!missing(id)) id <- as.character(id)
  if (!missing(id)) stopifnot(length(id) == 1)
  if (!missing(key)) key(x) <- key
  if (!missing(id)) .id(x) <- id
  res <- .as.state(x)
  arg <- .as.state(as.audited(data.frame(), id = '(audited)'))
  event <- .as.event('modify',arg,res)
  audit <- audit(x)
  last.agg <- rev(audit$res.agg)[[1]]
  last.rec <- rev(audit$res.rec)[[1]]
  if(
    !identical(
      as.numeric(event$res.agg),
      as.numeric(last.agg)
    ) || !identical(
      as.numeric(event$res.rec),
      as.numeric(last.rec)
    )
  ){
    audit(x) <- rbind(audit(x), event)
    artifact <- as.keyed(x)[0,,drop=FALSE]
    # if .artifact('modify') ... no interesting alternative
    artifact(x) <- c(artifact(x),list(artifact))
  }
  x
}
as.nm.audited <- function(x, key = match.fun('key')(x), id,...){
  if (!missing(key) && !(all(key %in% names(x))))warning('key columns not all in names(x)')
  if (!missing(id)) id <- as.character(id)
  if (!missing(id)) stopifnot(length(id) == 1)
  if (!missing(key)) key(x) <- key
  if (!missing(id)) .id(x) <- id
  y <- NextMethod()
  class(y) <- union(c('nm','audited'), class(y))
  audit(y) <- audit(x)
  artifact(y) <- artifact(x)
  .id(y) <- .id(x)
  key(y) <- key(x)
  y
}

`!.audited` <- function(e1)e1[dupKeys(e1) | naKeys(e1), , drop = FALSE]
`^.audited` <- function(e1,e2){
  y <- as.keyed(e1) ^ as.keyed(e2)
  class(y) <- class(e1)
  key(y) <- key(e1)
  audit(y) <- audit(e1)
  artifact(y) <- artifact(e1)
  .id(y) <- .id(e1)
  y
}
`|.audited` <- function(e1,e2){
  y <- as.keyed(e1) | as.keyed(e2)
  class(y) <- class(e1)
  key(y) <- key(e1)
  audit(y) <- audit(e1)
  .id(y) <- .id(e1)
  artifact(y) <- artifact(e1)
  y
}
Ops.audited <- function(e1,e2){
  if(.id(e1) == .id(e2) )warning('e1 and e2 have same id')
  supported <- c('+','*','-','&','/')
  op='unsupported'
  if(.Generic %in% c('+','*')) op='add'
  if(.Generic %in% c('-','&','/')) op='drop'
  y <- NextMethod(.Generic)
  #z <- if(.artifact()) as.keyed(e1) %-% as.keyed(x) else NULL # lost records
  loss <- suppressMessages(as.keyed(e1) - as.keyed(y))
  gain <- suppressMessages(as.keyed(y) - as.keyed(e1))
  change <- e2[0,,drop=FALSE]
  if(op == 'drop') change <- loss
  if(op == 'add') change <- gain
  #loss <- as.audited(loss, id = '(loss)')
  if(op=='drop') if(nrow(loss)) if(nrow(loss) != nrow(e1) - nrow(y))warning('record count: loss is not strictly the difference of original and result')
  if(op=='add')  if(nrow(gain)) if(nrow(gain) != nrow(y) - nrow(e1))warning('record count: gain is not strictly the difference of result and original')
  class(y) <- class(e1)
  .id(y) <- .id(e1)
  audit(y) <- audit(e1)
  artifact(y) <- artifact(e1)
  res <- .as.state(y)
  arg <- .as.state(e2) # Debatable whether to document the state of the input vs. the change, e.g. loss
  event <- .as.event(op,arg,res)
  if(.Generic %in% supported) {
    audit(y) <- rbind(audit(y),event)
    artifact(y) <- c(artifact(y), list(if(.artifact(op)) change else change[0,,drop=FALSE]))
  } else if(nrow(e1) != nrow(y))warning(.Generic,'(unsupported) has changed the number of rows')
  y
}
rbind.audited <- function(...,deparse.level = 1){
  args <- list(...)
  if (length(args) == 1) return (args[[1]])
  e1 <- args[[1]]
  e2 <- do.call(rbind, args[-1])
  if(.id(e1) == .id(e2) )warning('e1 and e2 have same id')
  op='add'
  y <- rbind.data.frame(e1,e2, deparse.level = deparse.level)
  class(y) <- class(e1)
  .id(y) <- .id(e1)
  audit(y) <- audit(e1)
  artifact(y) <- artifact(e1)
  res <- .as.state(y)
  arg <- .as.state(e2)
  event <- .as.event(op,arg,res)
  audit(y) <- rbind(audit(y),event)
  artifact(y) <- c(artifact(y), list(if(.artifact(op)) e2 else e2[0,,drop=FALSE]))
  y
}
`[.audited` <- function (x, i, j, drop, id, od){  
  # this function can be invoked with up to 6 arguments
  Nargs <- nargs()
  candidates <- names(formals())
  supplied <- intersect(candidates, names(match.call()))
  candidates <- setdiff(candidates, supplied)
  Nargs <- Nargs - length(supplied)
  implied <- candidates[seq_len(Nargs)]
  represented <- union(supplied , implied)
  dims <- intersect(c('i','j'), represented)
  # perhaps represented by an empty position, 
  # inflating Nargs relative to non-missing args
  dims <- length(dims)
  stopifnot(dims %in% 1:2)
  #if(missing(id)) id <- .id(x)
  if(missing(id)) id <- attr(x,'id')
  if(missing(od)) od <- paste('!',deparse(substitute(i)))[[1]]
  # NextMethod will not work because id, od cannot be suppressed
  y <- x
  class(y) <- c('keyed','data.frame') 
  mi <- missing(i)
  mj <- missing(j)
  op <- 'drop' # subsetting is a drop operation unless i exists and has duplicates
  if(!mi & dims == 2){ # groom i when it is the row subset criterion, to prohibit ambiguities
  	  # i must never be NA, because that creates irrelevant records interfering with the audit.
  	  if(any(is.na(i))) if( is.logical(i)){
  	  	  i[is.na(i)] <- FALSE
  	  } else {
  	  	  i <- i[!is.na(i)]
  	  }
  	  # i numeric must never be greater than nrow, because that returns NA records interfering with the audit.
  	  if(is.numeric(i)){
  	  	  greater <- i > nrow(y)
  	  	  if(any(greater)) i <- i[!greater]
  	  }
  	  # i character must be in row.names, so as not to return NA records.
  	  if(is.character(i)) i <- i[i %in% row.names(y)]
  	  # if i has dups (non-negative numeric), it is an 'add' operation and must not also be a 'drop' operation
  	  if(!is.logical(i)) if(anyDuplicated(i)) if(is.character(i) || any(i > 0)) { # an 'add' operation
  	  	  u <- unique(i)
  	  	  c <- if(is.character(i)) row.names(y) else seq_len(nrow(y)) # comparitor
  	  	  if(setequal(i, c)) op <- 'add'
  	  	  else stop('cannot simultaneously add and drop audited records')
  	  }	  	  
  }
  # now i is logical, character, or numeric, has no NA, and does not select repeated records unless all records are selected.
  # now there is a strict additive relationship between original records, resulting records, and difference.
  	  	  
  if(missing(drop)){
  	  if( dims == 1){
  	  	                  y <- y[i  ]
  	  } else {
  	  	  if(mj){
  	  	  	  if(mi){
  	  	  	  	  y <- y[ , ]
  	  	  	  } else {
  	  	  	  	  y <- y[i, ]
  	  	  	  }
  	  	  } else {
  	  	  	  if(mi){
  	  	  	          y <- y[ ,j]
  	  	  	 } else {
  	  	  	 	  y <- y[i,j]
  	  	  	 }
  	          }
  	 }
  	  	  	 
  } else {   #drop not missing 
  	  if( dims == 1){
  	  	                  y <- y[i,  drop=drop]
  	  } else {
  	  	  if(mj){
  	  	  	  if(mi){
  	  	  	  	  y <- y[ , ,drop=drop]
  	  	  	  } else {
  	  	  	  	  y <- y[i, ,drop=drop]
  	  	  	  }
  	  	  } else {
  	  	  	  if(mi){
  	  	  	  	  y <- y[ ,j,drop=drop]
  	  	  	  } else {
  	  	  	  	  y <- y[i,j,drop=drop]
  	  	  	  }
  	  	  }
  	  }
  }
  if(!inherits(y,'data.frame')) return(y)
  class(y) <- class(x) # a couple variants exist,  not safe to hard-code
  attr(y,'id') <- id
  res <- .as.state(y)
  rx <- as.character(attr(x,'row.names'))
  ry <- as.character(attr(y,'row.names'))
  diffIndex <- if(op=='drop')setdiff(rx, ry) else setdiff(ry,rx)
  diff <- if(op=='drop') x else y
  class(diff) <- 'data.frame'
  diff <- diff[diffIndex,,drop=FALSE]
  attr(diff,'id') <- od
  attr(diff,'key') <- attr(x,'key')
  class(diff) <- c('audited','keyed','data.frame')
  arg <- .as.state(diff)
  class(diff) <- c('keyed','data.frame')
  attr(diff,'id') <- NULL
  attr(diff,'audit') <- NULL
  attr(diff,'artifact') <- NULL
  audit(y) <- audit(x)
  artifact(y) <- artifact(x)
  if(nrow(diff)){
    audit(y) <- rbind(audit(y),.as.event(op,arg,res))
    artifact(y) <- c(artifact(y), list(if(.artifact(op)) diff else diff[0,,drop=FALSE])) 
  }
  y
}

combinations.audited <- function(x,...)combinations(as.keyed(x),...)
digest.audited <- function(x,...)digest(as.keyed(x),...)
as.digest.audited <- function(x,...)as.digest(as.keyed(x),...)
head.audited <- function (x, n = 6L, ..., id, od='! head'){
  stopifnot(length(n) == 1L)
  n <- if (n < 0L) 
    max(nrow(x) + n, 0L)
  else min(n, nrow(x))
  #if(missing(id)) return(x[seq_len(n), , drop = FALSE, od = od])
  x[seq_len(n), , drop = FALSE, id = id, od = od ]
}
tail.audited <- function (x, n = 6L, ..., id, od='! tail') {
  stopifnot(length(n) == 1L)
  nrx <- nrow(x)
  n <- if (n < 0L) 
    max(nrx + n, 0L)
  else min(n, nrx)
  #if(missing(id)) return (x[seq.int(to = nrx, length.out = n), , drop = FALSE, od=od])
  x[seq.int(to = nrx, length.out = n), , drop = FALSE, id = id, od = od ]
}
unique.audited <- function (x, incomparables = FALSE, fromLast = FALSE, id, od='! unique', ...) {
  if (!identical(incomparables, FALSE)) 
    .NotYetUsed("incomparables != FALSE")
  x[!duplicated(x, fromLast = fromLast, ...), , drop = FALSE, id = id, od = od ]
}
subset.audited <- function (x, subset, select, drop = FALSE, id, od= '! subset', ...){
  if (missing(subset)) 
    r <- TRUE
  else {
    e <- substitute(subset)
    r <- eval(e, x, parent.frame())
    if (!is.logical(r)) 
      stop("'subset' must be logical")
    r <- r & !is.na(r)
  }
  if (missing(select)) 
    vars <- TRUE
  else {
    nl <- as.list(seq_along(x))
    names(nl) <- names(x)
    vars <- eval(substitute(select), nl, parent.frame())
  }
  #if(missing(id)) return(x[r, vars, drop = drop, od=od])
  x[r, vars, drop = drop, id = id, od = od]
}
melt.audited <- function (
  data, 
  id.vars = key(data), 
  measure.vars, 
  variable_name = "variable", 
  na.rm = FALSE, 
  ...
){
  x <- NextMethod()
  class(x) <- class(data)
  .id(x) <- .id(data)
  .id(data) <- '(melt)'
  res <- .as.state(x)
  arg <- .as.state(data)
  event <- .as.event('transform',arg,res)
  audit(x) <- rbind(audit(data),event)
  artifact <- as.keyed(data)[0,,drop=FALSE]
  if(.artifact('transform')) artifact <- as.keyed(data)
  artifact(x) <- c(artifact(data),list(artifact))
  x
}
setOldClass(c('audited','keyed','data.frame'))
setMethod(
  'cast',
  'audited',
  function(
    data, 
    formula = ... ~ variable, 
    fun.aggregate=NULL, 
    check.names=FALSE,
    stringsAsFactors=FALSE,
    reclass=TRUE,
    ..., 
    margins=FALSE, 
    subset=TRUE, 
    df=FALSE, 
    fill=NA, 
    add.missing=FALSE, 
    value = reshape::guess_value(data)
  ){
    x <- callNextMethod()
    class(x) <- class(data)
    .id(x) <- .id(data)
    .id(data) <- '(cast)'
    res <- .as.state(x)
    arg <- .as.state(data)
    event <- .as.event('transform',arg,res)
    audit(x) <- rbind(audit(data),event)
    artifact <- as.keyed(data)[0,,drop=FALSE]
    if(.artifact('transform')) artifact <- as.keyed(data)
    artifact(x) <- c(artifact(data), list(artifact))
    x
  }
)
aggregate.audited <- function (x, by = x[, setdiff(key(x), across), drop = FALSE], 
          FUN, across = character(0), ...){
  y <- callNextMethod()
  class(y) <- class(x)
  .id(y) <- .id(x)
  .id(x) <-  '(aggregate)'
  res <- .as.state(y)
  arg <- .as.state(x)
  event <- .as.event('transform',arg,res)
  audit(y) <- rbind(audit(x),event)
  artifact <- as.keyed(x)[0,,drop=FALSE]
  if(.artifact('transform')) artifact <- as.keyed(x)
  artifact(y) <- c(artifact(x), list(artifact))
  y
}
merge.audited <- function(
	x, 
	y, 
	strict=TRUE,
	...
){
  #stopifnot(inherits(y,'audited'))
  y <- as.audited(y)
  if(.id(x) == .id(y) )warning('x and y have same id')
  op <- 'merge'
  z <- NextMethod()
  if(strict)if(nrow(suppressMessages(as.keyed(x)-as.keyed(z))))stop('cannot drop records from x when strict is TRUE')
  class(z) <- class(x)
  .id(z) <- .id(x)
  res <- .as.state(z)
  arg <- .as.state(y)
  audit <- audit(x)
  audit <- rbind(audit,.as.event(op,arg,res))
  audit(z) <- audit
  artifact <- as.keyed(y)[0,,drop=FALSE]
  if(.artifact(op)) artifact <- as.keyed(y)
  artifact(z) <- c(artifact(x), list(artifact))
  z
}

audit <- function(x,...)UseMethod('audit')
audit.audited <- function(x, ...)structure(attr(x,'audit'),class=c('audit','data.frame'))
`audit<-` <- function(x,value)UseMethod('audit<-')
`audit<-.audited` <- function(x,value){
  attr(x,'audit') <- value
  x
}
artifact <- function(x,...)UseMethod('artifact')
artifact.audited <- function(x, ...)structure(attr(x,'artifact'),class=c('artifact'))
`artifact<-` <- function(x,value)UseMethod('artifact<-')
`artifact<-.audited` <- function(x,value){
  attr(x,'artifact') <- value
  x
}
.id <- function(x,...)UseMethod('.id')
.id.audited <- function(x, ...)attr(x,'id')
`.id<-` <- function(x,value)UseMethod('.id<-')
`.id<-.audited` <- function(x,value){
  attr(x,'id') <- value
  x
}

as.xlsx <- function(x, ...)UseMethod('as.xlsx')
as.xlsx.audited <- function(x,file=NULL,...)as.xlsx(artifact(x),file=file,names=audit(x)$arg.id,...)
as.xlsx.artifact <- function(x,names,file=NULL,simplify=TRUE,gc=FALSE, ...){
  rowcount <- sapply(x,nrow)
  blank <- rowcount == 0
  if(simplify) x <- x[!blank]
  if(length(names) == length(blank) && simplify) names <- names[!blank]
  if(length(names) != length(x)) stop('number of names must be number of artifacts',if(simplify) 'with rows')
  names <- make.unique(names, sep = " ")
  require(xlsx)
  wb <- xlsx::createWorkbook()
  if(length(x) == 0){
  	  message('no qualifying artifacts')
  	  return(invisible(wb))
  }
  lapply(
    seq_along(names),
    function(i){
      sheet <- names[[i]]
      frame <- x[[i]]
      frame <- as.data.frame(frame)
      #frame[] <- lapply(frame,as.character)
      if(gc){
        gc()
        if(requireNamespace('rJava',quietly=TRUE))
        rJava::.jcall('java/lang/System',method='gc') 
      #http://stackoverflow.com/questions/21937640/handling-java-lang-outofmemoryerror-when-writing-to-excel-from-r
      }
      sheet <- xlsx::createSheet(wb,sheet)
      xlsx::addDataFrame(frame,sheet,row.names=FALSE)
    }
  )
  if(length(file)) xlsx::saveWorkbook(wb, file)
  if(length(file)) return(invisible(wb))
  wb
}

write.audit <- function(x, file, quote=FALSE, row.names=FALSE, na= '.', ...)write.csv(
  x,
  file=file,
  quote=quote,
  row.names=row.names,
  na=na,
  ...
)
read.audit <- function(x,...){
  y <- read.csv(x,na.strings='.',as.is=TRUE)
  class(y) <- c('audit','data.frame')
  y
}

as.igraph.audited <- function(x,attrs=list(),...)as.igraph(audit(x),attrs=attrs,...)
as.igraph.audit <- function(x,graph=graph.empty(),attrs=list(),...){
  if(nrow(x) == 0) {
    attr(graph,'tip') <- NULL
    layout <- get.graph.attribute(graph,'layout')
    if(!is.null(layout)) graph <- set.graph.attribute(graph,'layout',.normalize(layout,...))
    return(graph)
  }
  event <- .as.event.audit(x[1,])
  graph <- .post(event, graph=graph, attrs=attrs, ...)
  as.igraph(x[-1,],graph=graph,attrs=attrs,...)
}
plot.audited <- function(x,attrs=auditAttrs(x,...),...){
#plot.audited needs to be easy to use and easy to look at.
#the defaults need to be documented.
#need to be able to supply and override vertex subtype attributes
#need to be able to supply arbitrary attributes and arbitrary plot args
#need to be careful not to supply unrecognized plot args
# Now we supply no plot args, since everything (even accidental weird stuff) can be supplied as attributes.
# All we have is attrs, which could be an empty list, or custom, or output of auditAttrs ....
# It is a flat list for convenient construction.  Here, we nest it as expected by as.igraph etc.
# key words: vertex, edge, drop, add, merge, transform, create  
# attrs is a flat list; replace it with a nested list
  sublist <- function(attrs,token){
  	  nms <- names(attrs)
  	  regex <- glue('^',token,'\\.')
  	  pull <- grepl(regex,nms)
  	  found <- attrs[pull]
  	  lost <- attrs[!pull]
  	  names(found) <- sub(regex,'',names(found))
  	  found <- list(found)
  	  names(found) <- token
  	  out <- c(found,lost)
  	  out <- out[sapply(out,function(sub)length(sub) > 0)]
  	  out
  }  	  
  sublistShapes <- function(attrs){
  	  attrs <- sublist(attrs,'vertex')
  	  attrs <- sublist(attrs,'edge')
  	  attrs
  }
  attrs <- sublistShapes(attrs)
  for(feature in c('drop','add','merge','modify','transform','create')) attrs <- sublist(attrs,feature)
  for(feature in c('drop','add','merge','modify','transform','create'))if(feature %in% names(attrs)) attrs[[feature]] <- sublistShapes(attrs[[feature]])
  # At this point, all attributes have been collected into attrs.  But attrs is only intended to support edge and vertex attrs. We pull out the others and
  # pass them separately.
  #plot(as.igraph(x,attrs=attrs))
  standard <- names(attrs) %in% c('drop','add','merge','modify','transform','create','edge','vertex')
  shapeAttrs <- attrs[standard]
  plotAttrs <- attrs[!standard]
  args <- list(x=x,attrs=shapeAttrs)
  args <- c(args,plotAttrs)
  g <- do.call(as.igraph,args)
  #print(get.graph.attribute(g,'layout'))
  plot(g)
  plot(g,add=TRUE)
  invisible(attrs)
}

.normalize <- function(x,...)UseMethod('.normalize')  # see also "scale.default"
.normalize.matrix <- function(x,...){
	for(i in seq_len(ncol(x)))x[,i] <- .normalize(x[,i],...)
	x
}
.normalize.default <- function(x,margin=0,...){
  if(max(x) - min(x)==0) return(rep(0,length(x)))
  x <- x - min(x)
  x <- x / max(x)
  x <- x * (2- margin*2)
  x <- x - 1 + margin
  x
}
maxchar <- function(x,...)UseMethod('maxchar')
maxchar.audit <- function(x,...)maxChar(c(x$arg.id,x$res.id))

deconvolute <- function(x, y = x, a = 0.04621, b = -0.08554, ...)((a * y + b) * x) / ((a * x + b) * y) # vertex diameter nonproportional with vertex size
modulate <- function(x,...)modulation(structure(1,class=x))	
modulation <- function(x,...)UseMethod('modulation')
modulationRStudioGD <- function(x,t=min(dev.size()),...)119.2 * exp(-1.499 * t) + 1.539 # vertex diameter varies by device
rstudiogd <- function(x='modulation.RStudioGD', value=modulationRStudioGD, pos=1)assign(x=x,value=value,pos=pos)
modulation.default <- function(x,...) 1
distend <- function(x, y, ...) y / (0.4491 * x / (1.1679 + x)) # vertex size rel. to node spacing nonlinear with graph dimension
project <- function(x,...) 3.6416/x^2 + 0.2769 # vertex diameter nonlinear with page size
dev.name <- function()names(dev.cur())	

auditAttrs <- function(x=NULL,...)UseMethod('auditAttrs')
auditAttrs.audited <- function(x,...)auditAttrs(audit(x),...)
auditAttrs.audit <- function(
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
	vertex.scale =       dimension.scale * deconvolution * distention * projection * proportion * modulation,
	vertex.label.scale = dimension.scale * canvas.scale  * distention * projection * proportion * chars.scale,
	vertex.size = vertex.nominal * vertex.scale ^ scale,
	vertex.size2 = vertex.size / vertex.aspect ^ scale,
	vertex.label.cex = vertex.label.scale ^ scale,
	edge.width =      edge.scale ^ scale, 
	edge.arrow.size = edge.scale ^ scale,
	edge.arrow.width =  1,
	scale=TRUE,
	rescale=!scale,
	...
)auditAttrs(
	x=NULL,
	vertex.size=vertex.size,
	vertex.size2=vertex.size2,
	vertex.label.cex=vertex.label.cex,
	edge.width=edge.width,
	edge.arrow.size=edge.arrow.size,
	edge.arrow.width=edge.arrow.width,
	rescale=rescale,
	...
)
	
auditAttrs.default <- function(
	x,
	color = TRUE,
	vertex.shape = 'circle',
	vertex.size = 15,
	vertex.size2 = vertex.size,
	vertex.color = if (color) 'lightgreen' else NA,
	vertex.frame.color = if (color) NA else 'black',
	vertex.label.color = if (color) 'darkblue' else 'black',
	vertex.label.cex = 1,
	vertex.label.family = 'mono',
	edge.color = if (color) 'darkgreen' else 'black',
	edge.width = 1,
	edge.arrow.size = 1,
	edge.arrow.width = 1,
	edge.label.color = vertex.label.color,
	edge.label.cex = vertex.label.cex,
	#edge.label.family = vertex.label.family,
	create.vertex.color = if (color) 'gold' else NA,
	drop.vertex.color = if (color) 'pink' else NA,
	drop.edge.color = if (color) 'red' else 'black',
	drop.edge.label = if (color) NA else 'drop',
	add.vertex.color = if (color) 'lightblue' else NA,
	add.edge.color = if (color) 'blue' else 'black',
	add.edge.label = if (color) NA else 'add',
	merge.vertex.color = if (color) 'orchid' else NA,
	merge.edge.color = if (color) 'orchid4' else 'black',
	merge.edge.label = if (color) NA else 'merge',
	transform.edge.label = if (color) NA else '',
	modify.edge.label = if (color) NA else '',
	rescale = FALSE,
	...
){
	out <- list(
		rescale = rescale,
		color = color, 
		vertex.shape = vertex.shape,
		vertex.size = vertex.size,
		vertex.size2 = vertex.size2,
		vertex.color = vertex.color,
		vertex.frame.color = vertex.frame.color,
		vertex.label.color = vertex.label.color,
		vertex.label.cex = vertex.label.cex,
		vertex.label.family = vertex.label.family,
		edge.color = edge.color,
		edge.width = edge.width,
		edge.arrow.size = edge.arrow.size,
		edge.arrow.width = edge.arrow.width,
		edge.label.color = edge.label.color,
		edge.label.cex = edge.label.cex,
		#edge.label.family = edge.label.family,
		create.vertex.color = create.vertex.color,		
		drop.vertex.color = drop.vertex.color,
		drop.edge.color = drop.edge.color,
		drop.edge.label = drop.edge.label,
		add.vertex.color = add.vertex.color,
		add.edge.color = add.edge.color,
		add.edge.label = add.edge.label,
		merge.vertex.color = merge.vertex.color,
		merge.edge.color = merge.edge.color,
		merge.edge.label = merge.edge.label,
		transform.edge.label = transform.edge.label,
		modify.edge.label = modify.edge.label
	)
	out <- out[!sapply(out,is.null)]
	out <- c(out,list(...))
	#print(vertex.size)
	out
}

.post <- function(x,graph,attrs,...)UseMethod('.post')
.post.create <- function(x,graph,nm,attrs,...){
  res <- .as.state(x, arg=FALSE,...)
  graph <- .post(res,graph,.distill(attrs,'create'),...)
  graph
}
.post.modify <- function(x,graph,attrs,...){
  attrs <- .distill(attrs,'modify')
  if(!is.null(attrs$edge$label))if(!is.na(attrs$edge$label))
  if(attrs$edge$label == '') attrs$edge$label <- x$arg.id
  #x$res.id <- x$arg.id
  res <- .as.state(x, arg=FALSE,...)
  graph <- .post(res,graph,attrs,...)
  graph
}
.post.transform <- function(x,graph,attrs,...){
  attrs <- .distill(attrs,'transform')
  if(!is.null(attrs$edge$label))if(!is.na(attrs$edge$label))
  if(attrs$edge$label == '') attrs$edge$label <- x$arg.id
  #x$res.id <- x$arg.id
  res <- .as.state(x, arg=FALSE,...)
  graph <- .post(res,graph,attrs,...)
  graph
}
.post.add <- function(x,graph,attrs,...){
  arg <- .as.state(x, arg=TRUE,...)
  res <- .as.state(x, arg=FALSE,...) 
  graph <- .post(res,graph,.distill(attrs,'modify'),...)
  graph <- .post(arg,graph,.distill(attrs,'add'),to=FALSE, tip=FALSE, offset = 1,...)
  graph
}
.post.merge <- function(x,graph,attrs,...){
  arg <- .as.state(x, arg=TRUE,...)
  res <- .as.state(x, arg=FALSE,...) 
  graph <- .post(res,graph,.distill(attrs,'modify'),...)
  graph <- .post(arg,graph,.distill(attrs,'merge'),to=FALSE, tip=FALSE, offset = 1,...)
  graph
}
.post.drop <- function(x,graph,attrs,...){
  arg <- .as.state(x, arg=TRUE,...)
  res <- .as.state(x, arg=FALSE,...) 
  graph <- .post(arg,graph,.distill(attrs,'drop'), tip=FALSE, offset = -1, ...)
  graph <- .post(res,graph,.distill(attrs,'modify'), ...)
  graph
}
.post.state <- function(x,graph,attrs, to = TRUE, tip=TRUE, offset = 0,...){
  nt <- get.graph.attribute(graph,'tip') #tip index; unsupported if vertices are dropped
  graph <- add.vertices(graph,nv=1,label=format(x,...),attr=attrs$vertex)
  graph <- .extend.layout(graph,offset,tip)
  nm <- length(V(graph))
  indices <- c(nt,nm)
  if(!to) indices <- rev(indices)
  if(length(indices) == 2) graph <- add.edges(graph, indices, attr=attrs$edge)
  graph <- set.graph.attribute(graph,'tip', if(tip) nm else nt)
  for(nm in names(list(...))) graph <- set.graph.attribute(graph,nm, list(...)[[nm]])
  graph
}
.extend.layout <- function(graph,offset,tip){
  stopifnot(offset %in% -1:1)
  m <- get.graph.attribute(graph, 'layout')
  tip <- get.graph.attribute(graph,'tip')
  init <- is.null(tip)
  if(offset == 0 && !init) offset <- c(1,-1)
  at <- if(init) matrix(c(0,0),ncol=2) else m[tip,,drop=FALSE]
  addl <- at + offset
  m <- rbind(m, addl)
  graph <- set.graph.attribute(graph,'layout',m)
  graph
}
.push <- function(list,element,name){
  if(is.null(list)) list <- list()
  list[[name]] <- element
  list
}
.distill <- function(x, event){ # a list with possibly 'edge' and 'vertex' and possibly 'create', 'add', 'merge', 'drop', 'modify','transform' containing 'edge' and 'vertex'
  y <- x[c('vertex','edge') %n% names(x)]
  if(event %in% names(x)){
    trump <- x[[event]]
    if('vertex' %in% names(trump)) for (attr in names(trump$vertex)) y$vertex <- .push(y$vertex, trump$vertex[[attr]], attr )
    if('edge' %in% names(trump)) for (attr in names(trump$edge)) y$edge <- .push(y$edge, trump$edge[[attr]], attr )
  }
  y
}
format.state <- function(x,format='\n%l\n%r',...){
  a <- x$id
  agg <- x$agg
  rec <- x$rec
  if(is.na(agg)) agg <- ''
  #p <- do.call(paste,as.list(c(agg,rec,sep=delimstate[[3]])))
  #p <- paste(delimstate[[1]],p,delimstate[[5]])
  #out <- paste(a,p)
  out <- format
  out <- gsub('%l',a,out)
  out <- gsub('%a',agg,out)
  out <- gsub('%r',rec,out)
  out
}

