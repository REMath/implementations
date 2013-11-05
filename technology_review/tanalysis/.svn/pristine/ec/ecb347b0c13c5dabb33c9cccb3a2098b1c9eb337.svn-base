FRAMAC_SHARE=$(shell frama-c -print-path)
PLUGIN_NAME=taint-analysis
CC=ocamlc
CFLAGS=-I $(FRAMAC_SHARE)/lib -c
PREFLAGS=-for-pack $(PLUGIN_NAME)
PACKFLAGS=-pack -o $(PLUGIN_NAME).cmo
CP=cp -f
RM=rm -f

build: pack_alias pack

pack_alias: uref \
  setp \
  steensgaard \
  olf \
  golf \
  ptranal

pack: utils \
	printer \
	typeHelper \
	taintGamma \
	taintPrinter \
	taintCFGPrinter \
	taintTyping \
  vulnerableUtils \
	alias \
	taintPretty \
  vulnerablePrinter \
	slicePretty \
	taintInstructionComputer \
	taintConfigHelper \
	customTaintFlow sccCallgraph \
	sccCallgraph \
	taintResults \
	metricComputer \
	minReadMetrics \
	maxReadMetrics \
	minTaintMetrics \
	maxTaintMetrics \
	metricPretty \
  testPointsTo \
	taint 
	$(CC) $(PACKFLAGS) uref.cmo \
             setp.cmo \
             steensgaard.cmo \
             olf.cmo \
             golf.cmo \
             ptranal.cmo \
             utils.cmo \
					   printer.cmo \
					   typeHelper.cmo \
					   taintGamma.cmo \
					   taintPrinter.cmo \
					   taintCFGPrinter.cmo \
					   taintTyping.cmo \
             vulnerableUtils.cmo \
					   alias.cmo \
					   taintPretty.cmo \
             vulnerablePrinter.cmo \
					   slicePretty.cmo \
					   taintInstructionComputer.cmo \
					   taintConfigHelper.cmo \
					   customTaintFlow.cmo \
					   sccCallgraph.cmo \
					   taintResults.cmo \
					   metricComputer.cmo \
					   minReadMetrics.cmo \
					   maxReadMetrics.cmo \
					   minTaintMetrics.cmo \
					   maxTaintMetrics.cmo \
					   metricPretty.cmo \
             testPointsTo.cmo \
					   taint.cmo 

#PTRANALYSIS BEGINS HERE

uref: uref.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
setp: setp.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
steensgaard: steensgaard.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
olf: olf.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
golf: golf.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
ptranal: ptranal.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

#PTRANALYSIS ENDS HERE
             
xmlr: xmlr.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

sccCallgraph: sccCallgraph.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
utils: utils.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

printer: printer.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
typeHelper: typeHelper.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^	
	
taintGamma: taintGamma.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
taintTyping: taintTyping.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^  

taintPrinter: taintPrinter.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
taintCFGPrinter: taintCFGPrinter.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

vulnerableUtils: vulnerableUtils.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
alias: alias.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^	

taintPretty: taintPretty.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^	
	
slicePretty: slicePretty.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

vulnerablePrinter: vulnerablePrinter.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
  
taintInstructionComputer: taintInstructionComputer.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^  
	
taintConfigHelper: taintConfigHelper.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^  
	
customTaintFlow: customTaintFlow.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^  

taintResults: taintResults.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

metricComputer: metricComputer.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

minReadMetrics: minReadMetrics.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
maxReadMetrics: maxReadMetrics.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
minTaintMetrics: minTaintMetrics.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
maxTaintMetrics: maxTaintMetrics.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
metricPretty: metricPretty.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^

testPointsTo: testPointsTo.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
	
taint: taint.ml
	$(CC) $(PREFLAGS) $(CFLAGS) $^
    
install: build
	$(CP) $(PLUGIN_NAME).cmo $(FRAMAC_SHARE)/plugins 

uninstall:
	$(RM) $(FRAMAC_SHARE)/plugins/$(PLUGIN_NAME).cmo

clean:
	$(RM) *.cm* .depend frama_c_journal.ml


