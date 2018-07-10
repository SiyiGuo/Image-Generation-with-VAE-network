#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 128;
width = 256;
convChannel = 64;
kernel = 8;


lrelu = ElementwiseLayer[Max[Ramp[#], #*0.3]&];
encoder = NetChain[{
ReshapeLayer[{3,width,width}],
ConvolutionLayer[128, {4,4}, "Stride"->1, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
ConvolutionLayer[128, {4,4}, "Stride"->2, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
ConvolutionLayer[64, {2,2}, "Stride"->2, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
ConvolutionLayer[32, {1,1}, "Stride"->2, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
ConvolutionLayer[16, {1,1}, "Stride"->2, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
ConvolutionLayer[8, {1,1}, "Stride"->2, "PaddingSize"->1],
BatchNormalizationLayer[],
lrelu,
FlattenLayer[],
lrelu,
512
}];


mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];


decoder = NetChain[{
512,
lrelu,
1024,
lrelu,
8*16*16, 
lrelu,
ReshapeLayer[{8,16,16}],
DeconvolutionLayer[convChannel, {4,4}, "Stride"->2,"PaddingSize"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[32, {4,4}, "Stride"->2,"PaddingSize"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[16, {4,4}, "Stride"->2,"PaddingSize"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[3, {4,4}, "Stride"->2,"PaddingSize"->1],
BatchNormalizationLayer[],
LogisticSigmoid
}, "Input"->{nlatent}];


(*Assume input is {1,28,28}*)
(*output the real number as wll*)
imageLoss = NetGraph[
{ElementwiseLayer[-1*# &, "Input"->{3,width,width}], TotalLayer[], ElementwiseLayer[#^2&], SummationLayer[]},
{
NetPort["inDec"]->1->2,
NetPort["inInput"]->2,
2->3->4
}
];


latentLoss = NetGraph[
{ElementwiseLayer[-0.5*#&], TotalLayer[], ElementwiseLayer[-(#^2)&], ElementwiseLayer[-Exp[2*#]&], ElementwiseLayer[1+2*#&],SummationLayer[], ElementwiseLayer[0*#&]},
{
NetPort["mn"]->3,
NetPort["sd"]->4,
NetPort["sd"]->5,
3->2,
4->2,
5->2,
2->6,
6->1
}
];


loss = ThreadingLayer[(#1+#2) / 2&, "Output"->"Real"];


vaeNet = NetInitialize[NetGraph[
<|"enc"->encoder,
"mn"->mn,
"sd"-> sd,"expSd"->expSd,"sdEpsilon"->ThreadingLayer[Times],
"z"->TotalLayer[],
"dec"->decoder,
"imageLoss"->imageLoss,
"latentLoss"->latentLoss,
"loss"->loss
|>,

{
NetPort["Input"]->"enc",
"enc"->"mn",
 "enc"->"sd", 
"sd"->"expSd","expSd"->"sdEpsilon", NetPort["random"] ->"sdEpsilon",
"mn"->"z", 
"sdEpsilon"->"z",
"z"->"dec",
"dec"->NetPort["Output"],
(*latent loss*)
"sd"->NetPort["latentLoss","sd"],
"mn"->NetPort["latentLoss","mn"],
(*image loss*)
"dec"->NetPort["imageLoss", "inDec"],
NetPort["Input"]->NetPort["imageLoss", "inInput"],
(*Total loss8*)
"latentLoss"->NetPort["loss", "1"],
"imageLoss"->NetPort["loss", "2"],
"loss"->NetPort["MeanLoss"]
},
"Output"->NetDecoder[{"Image", "RGB"}],
"Input"->NetEncoder[{"Image", {width, width}, "RGB"}]
]];


imagePaths = Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg",FileNameJoin[{NotebookDirectory[], "DataMonet"}]]];
dataSets = Map[Import[#]&, imagePaths];
trainingData =<|"random"->RandomVariate[NormalDistribution[],{Length@dataSets,nlatent}],
"Input"->dataSets|>


dir = CreateDirectory[]


(*vaeNet*)
SetDirectory[NotebookDirectory[]]
trainedVae = NetTrain[vaeNet, trainingData, LossFunction->{"MeanLoss"->Scaled[1]},
MaxTrainingRounds->2000,
TrainingProgressReporting->"Panel",
Method->{"ADAM", "LearningRate"->0.0005},
TrainingProgressCheckpointing->{"Directory", dir, "Interval"->Quantity[50, "Rounds"]},
TargetDevice->"GPU",
 BatchSize->16]
 Export["smallNewMonet.wlnet", trainedVae]






