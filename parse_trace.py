#GVSoC trace files input
f1 = open("traces_pip_16cl.txt", 'r')
#testbench dma input traces
f2 = open("traces_pip_16cl_tb.txt", 'w+')
total_bytes=0
f1_lines = f1.readlines()
for l in f1_lines:
        try:
                key_word1 = list(l.split())[2]
                key_word2 = list(l.split())[11]
                key_word3 = list(l.split())[13]
                key_word4 = list(l.split())[15]
                if key_word1[-1] == 'e':
                        if key_word1[29] == '/':
                            f2.write('0'+' '+key_word2[:-1]+' '+key_word3[:-1]+' '+key_word4[:-1]+'\n')
                            total_bytes = total_bytes + int(key_word4[2:-1], base=16)
                            #print(int(key_word4[2:-1], base=16))
                        elif key_word1[29] == '_':
                            if key_word1[31] == '/':
                                f2.write(key_word1[30]+' '+key_word2[:-1]+' '+key_word3[:-1]+' '+key_word4[:-1]+'\n')
                                total_bytes = total_bytes + int(key_word4[2:-1], base=16)
                                #print(int(key_word4[2:-1], base=16))
                            else:
                                f2.write(key_word1[30:32]+' '+key_word2[:-1]+' '+key_word3[:-1]+' '+key_word4[:-1]+'\n')
                                total_bytes = total_bytes + int(key_word4[2:-1], base=16)
        except:
                continue

print(total_bytes)
f1.close()
f2.close()
