workingDir = ""
TH_f = 0.7
TH_score = 0.2

varSavePath = workingDir+"/SaveVar/"
projectSavePath = workingDir+"/ProjectInfo/"
cmdRun = True
OnlyReadFlag = True
CallPathDiff = False
LogEHRRFlag = True
DetailAnalysis = True
setGlobalContext = False#flag use for cross-project learn
loadAllVarFlag = False#flag use for cross-project learn
MeteTrainMinGroupNum = 2
VarTrainMinGroupNum = 2
FindedBugPath = ""
def ConfigFunc():
    BasicPath = "StructInfo/"
    projectBasicPath = workingDir + "/Test/"
    fileTypes = ["c", "h"]
    pInfoList = []
    pPathList, patternListList = SigProjectDivide(pInfoList)
    projectPathList = []
    for i in pPathList:
        projectPathList.append(projectBasicPath + i)
    return pPathList, projectPathList, patternListList, BasicPath, fileTypes, TH_score

def SigProjectDivide(pInfoList):
    pPathList = []
    patternListList = []
    for sigpi in pInfoList:
        pPathList.append(sigpi[0])
        patternListList.append(sigpi[1:])
    return pPathList, patternListList