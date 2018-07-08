#!/usr/bin/env wolframscript
(* ::Package:: *)

Echo["Import Net"];
continueVae = Import["monetVae.wlnet"];
dir = CreateDirectory[];
Echo[dir];
imagePaths=Map[StringReplace[#,"\\"->"/"]&,FileNames["*.jpg","Monet"]];
dataSets=Map[Import[#]&,imagePaths];
Echo[Length@dataSets]
trainingData=<|"random"->RandomVariate[NormalDistribution[],{Length@dataSets,nlatent}],"Input"->dataSets|>;
trainedVae=NetTrain[continueVae,trainingData,
LossFunction->{"latentLoss"->Scaled[1],"imageLoss"->Scaled[1]},MaxTrainingRounds->2000,
TrainingProgressReporting->"Print",Method->{"ADAM","LearningRate"->0.00005},
TargetDevice->"GPU",TrainingProgressCheckpointing->{"Directory",dir,"Interval"->Quantity[100,"Rounds"]},
BatchSize->32];
Export["monetVae2.wlnet",trainedVae];
