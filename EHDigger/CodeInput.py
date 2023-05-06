import os

def getCodeList(path, fileTypes):
    fileList = []
    fileTypeList = []
    if os.path.isfile(path):
        pLen = len(path)
        if (pLen>0):
            pos = path.rfind(".")
            if pos!=-1:
                curType = path[pos+1:]
                if (curType in fileTypes):
                    #print("path", path)
                    fileList.append(path)
                    fileTypeList.append(curType)

    elif os.path.isdir(path):
        for s in os.listdir(path):
            newDir = os.path.join(path, s)
            a, b = getCodeList(newDir, fileTypes)
            fileList.extend(a)
            fileTypeList.extend(b)
    return fileList, fileTypeList

def CodeInput(Filelist):
    codeList = []
    for sigFile in Filelist:
        try:
            file = open(sigFile, 'r',encoding = 'UTF-8')
            fileContent = file.read()
        except UnicodeDecodeError:
            continue
        codeList.append(fileContent)
        file.close()
    return codeList

def getCode(path, fileTypes):
    fileList, fileTypeList = getCodeList(path, fileTypes)
    codeList = CodeInput(fileList)
    return fileList, codeList, fileTypeList
