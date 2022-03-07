/*
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <algorithm>
#include <string>
#include <vector>
#include <fstream>
#include <iostream>

#include <sys/wait.h>
#include <unistd.h>
#include <cstdlib>
#include <csignal>
#include <cstring>
#include <fcntl.h>

int main(int argc, char** argv) {
    std::vector<pid_t> children;

    if (argc < 5) throw std::logic_error("Not enough arguments provided");
    std::string file = argv[1];
    std::string logic = argv[2];
    std::vector<std::string> engines;
    for (int i = 3; i < argc; ++i) {
        engines.push_back(argv[i]);
    }

//    std::cout << "File: " << file << '\n';
//    std::cout << "Logic: " << logic << '\n';
//    std::cout << "Engines:\n";
//    for (auto engine : engines) {
//        std::cout << engine << '\n';
//    }

    for (auto const & engine : engines) {
        pid_t child_pid = fork();
        if (child_pid == 0) {
            std::string engineFile = engine + ".out";
            int fd = open(engineFile.c_str(), O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
            dup2(fd, 1);   // make stdout go to file
            dup2(fd, 2);   // make stderr go to file
            close(fd);
            std::string logicArg = "--logic=" + logic;
            std::string engineArg = "--engine=" + engine;
            execlp("./golem", "./golem", logicArg.c_str(), engineArg.c_str(), file.c_str() ,(char*)NULL);
            printf("execl failed - %s\n", strerror(errno));
            exit(1);
        } else if (child_pid > 0) {
//            std::cout << "Engine " << engine << " got pid " << child_pid << std::endl;
            children.push_back(child_pid);
        } else {
            perror("fork");
            exit(1);
        }
    }
    pid_t wid;
    while ((wid = wait(NULL)) > 0) {
//        std::cout << "Awoken by " << wid << std::endl;
        // check if we have answer in a file
        for (auto const & engine : engines) {
            std::fstream in(engine + ".out");
            if (in.is_open()) {
                std::string a;
                in >> a;
                in.close();
                if (a == "sat" or a == "unsat") {
                    std::cout << a << std::endl;
                    // kill all remaining processes
                    for (auto child : children) {
//                        std::cout << "Killing process " << child << std::endl;
                        kill(child, SIGKILL);
                    }
                    return 0;
                } else {
//                    std::cout << "Read " << a << std::endl;
                }
            }
        }
        children.erase(std::find(children.begin(), children.end(), wid));
    }
    std::cout << "unknown" << std::endl;
}
