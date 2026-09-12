package exec

import (
	"os/exec"
	"syscall"

	"github.com/zouuup/landrun/internal/log"
)

func Run(args []string, env []string) error {
	binary, err := exec.LookPath(args[0])
	if err != nil {
		return err
	}

	log.Info("Executing: %v", args)

	// Only pass the explicitly specified environment variables
	// If env is empty, no environment variables will be passed
	return syscall.Exec(binary, args, env)
}
