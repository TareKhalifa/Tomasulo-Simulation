#include <iostream>
#include <string>
#include <queue>
#include <vector>
#include <fstream>
#include <map>
using namespace std;
string filename = "file.txt";
int Cycles = 0;
int PcNumber = 0;
int PC = 0;
int issueCounter = 0;
bool beqCounter = false;
bool lastIssued = false;
int totalBranches = 0;
int falseBranches = 0;
double missRatio = 0;
int written = 0;
struct RS {
	string name;	
	string op;
	bool busy;
	int cyclesLeft;
	string Qj;
	string Qk;
	int Vj;
	int Vk;
	int A;
	int cycleIssued;
	int rd;
	int PC;
	bool beq;
};
struct inst {
	string type;
	string rd;
	string rs1;
	string rs2;
	int imm;
	int PCvalue;
	int fetch;
};
vector<inst> instVector;
queue<inst> buffer;
RS r[15];
string RAT[8];
bool RAT2[8];
int rf[8];
map<string , int> myLabels;
int memory[64 * 1024];
void clearEntry(int writeaddr)
{
	r[writeaddr].busy = 0;
	r[writeaddr].op = "-1";
	r[writeaddr].Qj = "-1";
	r[writeaddr].Qk = "-1";
	r[writeaddr].Vj = -1;
	r[writeaddr].Vj = -1;
	r[writeaddr].cyclesLeft = -1;
	r[writeaddr].A = -1;
	r[writeaddr].rd = -1;
	r[writeaddr].PC = -1;
	r[writeaddr].beq = 0;

}
void clearBeq(int writeaddr)
{
	r[writeaddr].beq = 0;
}
bool rEmpty()
{
	for (int i = 0; i < 15; i++)
		if (r[i].busy)
			return false;
	return true;
}
int checkAvaialability(inst current)
{
	if (current.type == "lw")
	{
		if (r[0].busy == 0)
			return 0;
		else if (r[1].busy == 0)
			return 1;
		else return -1;
	}
	if (current.type == "sw")
	{
		if (r[2].busy == 0)
			return 2;
		else if (r[3].busy == 0)
			return 3;
		else return -1;
	}
	if (current.type == "ret" || current.type == "jalr" || current.type == "jmp")
	{
		if (r[4].busy == 0)
			return 4;
		else if (r[5].busy == 0)
			return 5;
		else if (r[6].busy == 0)
			return 6;
		else return -1;
	}
	if (current.type == "beq")
	{
		if (r[7].busy == 0)
			return 7;
		else if (r[8].busy == 0)
			return 8;
		else return -1;
	}
	if (current.type == "add" || current.type == "addi" || current.type == "sub")
	{
		if (r[9].busy == 0)
			return 9;
		else if (r[10].busy == 0)
			return 10;
		else if (r[11].busy == 0)
			return 11;
		else return -1;
	}
	if (current.type == "nand")
	{
		if (r[12].busy == 0)
			return 12;
		else return -1;
	}
	if (current.type == "mul")
	{
		if (r[13].busy == 0)
			return 13;
		else if (r[14].busy == 0)
			return 14;
		else return -1;
	}
}
void RsEdit(int x,inst current)
{
	if (x != -1) {
		if (current.fetch != Cycles) {
			r[x].cyclesLeft = -1;
			r[x].busy = 1;
			r[x].op = current.type;
			r[x].cycleIssued = Cycles;
			r[x].PC = current.PCvalue;
			if (current.PCvalue == instVector.size() - 1)
				lastIssued = true;
			if (beqCounter)
				r[x].beq = 1;
			int rdNumber = -1;

			if (current.type == "add" || current.type == "sub" || current.type == "mul" || current.type == "nand")
			{
				int RegNum1 = stoi(current.rs1.substr(1));
				int RegNum2 = stoi(current.rs2.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				if (RAT[RegNum2] == "-1")
				{
					r[x].Vk = rf[RegNum2];
					r[x].Qk = "-1";
				}
				else
					r[x].Qk = RAT[RegNum2];
				int RegNum3 = stoi(current.rd.substr(1));
				if (r[x].beq)
					RAT2[RegNum3] = 1;
				RAT[RegNum3] = r[x].name;
				rdNumber = RegNum3;
			}
			else if (current.type == "addi")
			{
				int RegNum1 = stoi(current.rs2.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				r[x].Qk = "-1";
				r[x].Vk = current.imm;
				int RegNum3 = stoi(current.rs1.substr(1));
				RAT[RegNum3] = r[x].name;
				if (r[x].beq)
					RAT2[RegNum3] = 1;
				rdNumber = RegNum3;
			}
			else if (current.type == "lw")
			{
				int RegNum1 = stoi(current.rs1.substr(1));
				RAT[RegNum1] = r[x].name;
				int RegNum2 = stoi(current.rs2.substr(1));
				if (RAT[RegNum2] == "-1")
				{
					r[x].Vj = rf[RegNum2];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum2];
				r[x].A = current.imm;
				rdNumber = RegNum1;
				if (r[x].beq)
					RAT2[RegNum1] = 1;
			}
			else if (current.type == "sw")
			{
				int RegNum1 = stoi(current.rs1.substr(1));
				int RegNum2 = stoi(current.rs2.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				if (RAT[RegNum2] == "-1")
				{
					r[x].Vk = rf[RegNum2];
					r[x].Qk = "-1";
				}
				else
					r[x].Qk = RAT[RegNum2];
				r[x].A = current.imm;
			}
			else if (current.type == "jmp")
			{
				r[x].Vk = current.imm;
				while (!buffer.empty())
					buffer.pop();
				PC = current.PCvalue + current.imm + 1;

			}
			else if (current.type == "beq")
			{
				beqCounter = true;
				int RegNum1 = stoi(current.rs1.substr(1));
				int RegNum2 = stoi(current.rs2.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				if (RAT[RegNum2] == "-1")
				{
					r[x].Vk = rf[RegNum2];
					r[x].Qk = "-1";
				}
				else
					r[x].Qk = RAT[RegNum2];
				r[x].A = current.imm;
				if (current.imm < 0)
				{
					PC = current.PCvalue + current.imm + 1;
					while (!buffer.empty())
						buffer.pop();
				}
				else PC = current.PCvalue + 1;

			}
			else if (current.type == "jalr")
			{
				int RegNum1 = stoi(current.rs1.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				int RegNum3 = stoi(current.rd.substr(1));
				RAT[RegNum3] = r[x].name;
				rdNumber = RegNum3;
				if (r[x].beq)
					RAT2[RegNum3] = 1;
				issueCounter = 2;
			}
			else if (current.type == "ret")
			{
				int RegNum1 = stoi(current.rs1.substr(1));
				if (RAT[RegNum1] == "-1")
				{
					r[x].Vj = rf[RegNum1];
					r[x].Qj = "-1";
				}
				else
					r[x].Qj = RAT[RegNum1];
				issueCounter = 2;
			}
			r[x].rd = rdNumber;
			if (!buffer.empty())
				buffer.pop();
		}
	}

}
void initialze()
{
	for (int i = 0; i < 15; i++)
	{
		r[i].busy = 0;
		r[i].op = "-1";
		r[i].Qj = "-1";
		r[i].Qk = "-1";
		r[i].Vj = -1;
		r[i].Vj = -1;
		r[i].cyclesLeft = -1;
		r[i].A = -1;
	}
	{
		r[0].name = "LD1";
		r[1].name = "LD2";
		r[2].name = "SW1";
		r[3].name = "SW2";
		r[4].name = "J1";
		r[5].name = "J2";
		r[6].name = "J3";
		r[7].name = "BEQ1";
		r[8].name = "BEQ2";
		r[9].name = "ADD1";
		r[10].name = "ADD2";
		r[11].name = "ADD3";
		r[12].name = "NAND1";
		r[13].name = "MULT1";
		r[14].name = "MULT2";
	}
	for (int i = 0; i < 8; i++)
		rf[i] = 0;
	for (int i = 0; i < 8; i++)
		RAT[i] = "-1";
	for (int i = 0; i < 8; i++)
		RAT2[i] = 0;
}
void parse() {
	ifstream ifile;
	ifile.open(filename.c_str());
	inst in;
	string s;
	string label;
	while (s!="endend")
	{
		getline(ifile, s);
		if (s.find(':') != string::npos)
		{
			label = s.substr(0, s.find(':'));
			s = s.substr(s.find(':') + 2);
			myLabels.insert({ label,PcNumber });
		}
		if (s.find("jmp")!=string::npos)
		{
			in.type = "jmp";
			s = s.substr(s.find("p") + 2);
			in.rd = s;
			in.PCvalue = PcNumber;
		}
		else if (((s.find("add") != string::npos) || (s.find("sub") != string::npos) || (s.find("nand") != string::npos) || (s.find("mul") != string::npos)) && (s.find("addi") == string::npos))
		{
			in.type = s.substr(0,s.find("R")-1);
			in.rd = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.rs1 = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.rs2 = s.substr(s.find("R"), 2);
		}
		else if ((s.find("addi") != string::npos) || (s.find("lw") != string::npos) || (s.find("sw") != string::npos))
		{
			in.type = s.substr(0, s.find("R") - 1);
			in.rs1 = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.rs2 = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.imm = stoi(s);
		}
		else if ((s.find("beq") != string::npos))
		{
			in.type = s.substr(0, s.find("R") - 1);
			in.rs1 = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.rs2 = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 2);
			in.rd = s;

		}
		else if (s.find("jalr")!=string::npos)
		{
			in.type = s.substr(0, s.find("R") - 1);
			in.rd = s.substr(s.find("R"), 2);
			s = s.substr(s.find(",") + 1);
			in.rs1 = s.substr(s.find("R"), 2);
		}
		else if (s.find("ret") != string::npos)
		{
			in.type = s.substr(0, s.find("R") - 1);
			in.rs1 = s.substr(s.find("R"), 2);
		}
		if (s != "endend")
		{
			in.PCvalue = PcNumber;
			instVector.push_back(in);
			PcNumber++;
		}
	}
	getline(ifile, s);
	PC = stoi(s.substr(s.find('=') + 2));
	while (!ifile.eof())
	{
		getline(ifile, s);
		int address; int value;
		address = stoi(s.substr(0, s.find(',')));
		value = stoi(s.substr(s.find(',')+2));
		memory[address] = value;
	}
	for (int i = 0; i < PcNumber; i++)
		if (instVector[i].type == "jmp")
			instVector[i].imm = (myLabels[instVector[i].rd] - instVector[i].PCvalue) - 1;
		else if(instVector[i].type == "beq")
			instVector[i].imm = (myLabels[instVector[i].rd] - instVector[i].PCvalue) - 1;
}	
void issue()
{
	inst current;
	if (!buffer.empty())
	{
		current = buffer.front();
		RsEdit(checkAvaialability(current), current);
	}
}
void execute()
{
	for (int i = 0; i < 15; i++)
	{
		if (r[i].busy)
		{
			if (r[i].cyclesLeft == 0 || r[i].beq)
			{
			}
			else if (r[i].cyclesLeft == -1)
			{
				if (r[i].Qj == "-1" && r[i].Qk == "-1")
				{
					if (i == 0 || i == 1 || i == 2 || i == 3 || i == 9 || i == 10 || i == 11)
						r[i].cyclesLeft = 2;
					else if (i == 4 || i == 5 || i == 6 || i == 7 || i == 8 || i==12)
						r[i].cyclesLeft = 1;
					else 
						r[i].cyclesLeft = 8;
				}
			}
			else r[i].cyclesLeft--;
		}
	}
}
void fetch()
{
	if (buffer.size() < 4 && PC < PcNumber)
	{
		inst b;
		b = instVector[PC];
		b.fetch = Cycles;
		buffer.push(b);
		PC++;
	}
	}
void write()
{
	int minimum = 30000;
	int writeaddr =-1;
	for (int i = 0; i < 15; i++)
	{
		if(r[i].cyclesLeft==0)
			if (r[i].cycleIssued < minimum)
			{
				minimum = r[i].cycleIssued;
				writeaddr = i;
			}
	}
	if (minimum != 30000)
	{
		written++;
		int result = 0;
		if (writeaddr == 0 || writeaddr == 1) //load
		{
			r[writeaddr].A += r[writeaddr].Vk;
			result = memory[r[writeaddr].A];
			rf[r[writeaddr].rd] = result;
			RAT[r[writeaddr].rd] = "-1";
			for (int i = 0; i < 15; i++)
			{
				if (r[i].Qj == r[writeaddr].name)
				{
					r[i].Vj = result;
					r[i].Qj = "-1";
				}
				if (r[i].Qk == r[writeaddr].name)
				{
					r[i].Vk = result;
					r[i].Qk = "-1";
				}
			}
		}
		else if (writeaddr == 2 || writeaddr == 3) //store
		{
			r[writeaddr].A += r[writeaddr].Vk;
			memory[r[writeaddr].A] = r[writeaddr].Vj;
		}
		else if (writeaddr == 4 || writeaddr == 5 || writeaddr == 6) //J, jalr, ret
		{
			if (r[writeaddr].op == "jmp")
			{
			}
			else if (r[writeaddr].op == "jalr")
			{
				rf[r[writeaddr].rd] = r[writeaddr].PC;
				PC = r[writeaddr].Vj;
				while (!buffer.empty())
					buffer.pop();
				for (int i = 0; i < 15; i++)
				{
					if (r[i].Qj == r[writeaddr].name)
					{
						r[i].Vj = r[writeaddr].PC;
						r[i].Qj = "-1";
					}
					if (r[i].Qk == r[writeaddr].name)
					{
						r[i].Vk = r[writeaddr].PC;
						r[i].Qk = "-1";
					}
				}
				RAT[r[writeaddr].rd] = "-1";
			}
			else if (r[writeaddr].op == "ret")
			{
				PC = r[writeaddr].Vj;
				while (!buffer.empty())
					buffer.pop();
			}
		}
		else if(writeaddr == 7 || writeaddr == 8) //beq
		{
			beqCounter = false;
			totalBranches++;
			result = r[writeaddr].Vj - r[writeaddr].Vk;
			if (r[writeaddr].A > 0)
			{
				if (result == 0)
				{
					for (int i = 0; i < 15; i++)
						if (r[i].beq)
							clearEntry(i);
					while (!buffer.empty())
						buffer.pop();
					PC = r[writeaddr].PC+ r[writeaddr].A+1;
					falseBranches++;
				}
				else
					for (int i = 0; i < 15; i++)
						if (r[i].beq)
							clearBeq(i);
			}
			else if (r[writeaddr].A < 0)
			{
				if (result != 0)
				{
					for (int i = 0; i < 15; i++)
						if (r[i].beq)
							clearEntry(i);
					while (!buffer.empty())
						buffer.pop();
					PC = r[writeaddr].PC+1;
					falseBranches++;
				}
				else
					for (int i = 0; i < 15; i++)
						if (r[i].beq)
							clearBeq(i);
			}
			for (int i = 0; i < 15; i++)
					clearBeq(i);
			for (int i = 0; i < 15; i++)
			if (RAT2[i] == 1)
			{
				RAT2[i] = 0;
				RAT[i] = "-1";
			}
			}
		else
		{
			if (r[writeaddr].op == "add")
				result = r[writeaddr].Vj + r[writeaddr].Vk;
			else if (r[writeaddr].op == "sub")
				result = r[writeaddr].Vj - r[writeaddr].Vk;
			else if (r[writeaddr].op == "mul")
				result = r[writeaddr].Vj * r[writeaddr].Vk;
			else if (r[writeaddr].op == "addi")
				result = r[writeaddr].Vj + r[writeaddr].Vk;
			else if (r[writeaddr].op == "nand")
			{
				result = r[writeaddr].Vj & r[writeaddr].Vk;
				result = ~result;
			}
			RAT[r[writeaddr].rd] = "-1";
			rf[r[writeaddr].rd] = result;
			for (int i = 0; i < 15; i++)
			{
				if (r[i].Qj == r[writeaddr].name)
				{
					r[i].Vj = result;
					r[i].Qj = "-1";
				}
				if (r[i].Qk == r[writeaddr].name)
				{
					r[i].Vk = result;
					r[i].Qk = "-1";
				}
			}
		}
		clearEntry(writeaddr);
	}
}
int main()
{
	parse();
	initialze();
	while (!rEmpty() || !lastIssued) 
	{
		rf[0] = 0;
		fetch();
		rf[0] = 0;	
		if (issueCounter == 0 && Cycles != 0)
			issue();
		rf[0] = 0;
		execute();
		rf[0] = 0;
		write();
		rf[0] = 0;
		if (issueCounter > 0)
			issueCounter--;
		Cycles++;
	}
	missRatio = double(falseBranches) / double(totalBranches);
	cout << "The total number of cycles is: " << Cycles << endl;
	if (totalBranches != 0)
		cout << "The total number of branches is: " << totalBranches << "\nThe misprediction ratio is: "<< missRatio << endl;
	cout << "The IPC is: " << double(written) / double(Cycles) << endl;
	system("pause");
}