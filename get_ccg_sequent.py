import os
path = "/p/cl/CCGbank/data/AUTO/"

for folder in [23]:
    open_path = path+str(folder)
    for filename in os.listdir(open_path):
        with open(open_path+"/"+str(filename), 'r') as f:
            for i,line in enumerate(f.readlines()):
                # print(i,line)
                cats = []
                if i%2==0:
                    l = line.split()
                    print(l[0])
                else:
                    l = line.split()
                    for idx,item in enumerate(l):
                        if item=="(<L":
                            cats.append(l[idx+1])
                    print(" ".join(cats)+" -> "+ l[1])
            exit()