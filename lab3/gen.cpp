#include <iostream>
#include <fstream>
#include <random>
#include <vector>
#include <cstdint>

std::string GenerateRandomString(size_t length)
{
    const std::string characters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    std::random_device randomDevice;
    std::mt19937 generator(randomDevice());
    std::uniform_int_distribution<> distribution(0, characters.size() - 1);

    std::string randomString;
    for (size_t i = 0; i < length; ++i) {
        randomString += characters[distribution(generator)];
    }

    return randomString;
}

int main(int argc, char const *argv[])
{
    std::string fileName;
    int n;

    std::cin >> fileName >> n;
    std::ofstream output(fileName);
    output.write(GenerateRandomString(n).c_str(), n);
    output.close();
    return 0;
}
