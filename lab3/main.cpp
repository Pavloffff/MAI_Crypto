#include <iostream>
#include <fstream>
#include <string>
#include <set>
#include <vector>
#include <iomanip>
#include <filesystem>
#include <algorithm>

int main(int argc, char const *argv[])
{
    std::string fileName1, fileName2;
    std::cout << "Enter 1st file name: ";
    std::cin >> fileName1;
    std::cout << "Enter 2nd file name: ";
    std::cin >> fileName2;

    std::ifstream input1(fileName1);
    std::ifstream input2(fileName2);
    
    int size1 = std::filesystem::file_size(fileName1);
    int size2 = std::filesystem::file_size(fileName2);

    std::string text1, text2;
    for (int i = 0; i < std::min(size1, size2); i++) {
        char t1 = input1.get();
        char t2 = input2.get();
        if (tolower(t1) >= 'a' && tolower(t1) <= 'z') {
            text1.push_back(tolower(t1));
        }
        if (tolower(t2) >= 'a' && tolower(t2) <= 'z') {
            text2.push_back(tolower(t2));
        }
    }
    
    int cntSames = 0, sz = std::min(text1.size(), text2.size());
    for (int i = 0; i < sz; i++) {
        if (text1[i] == text2[i]) {
            cntSames++;
        }
    }

    double result = (static_cast<double>(cntSames) / static_cast<double>(sz)) * 100;

    std::cout << result << "\n";

    input1.close();
    input2.close();
    return 0;
}
